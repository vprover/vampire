
/*
 * File Storage.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Storage.cpp
 * Implements class Storage.
 */

#include <malloc.h>
#include <string.h>
#include <libmemcached/memcached.h>

#include "Debug/Assertion.hpp"
#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Int.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Storage.hpp"

namespace Shell
{
namespace LTB
{

using namespace Lib;
using namespace Kernel;

const unsigned Storage::storedIntMaxSize;

class Storage::StorageImpl
{
public:
  StorageImpl()
  {
    CALL("Storage::StorageImpl::StorageImpl");

    memc=memcached_create(&memcObj);
    ASS_EQ(memc, &memcObj);

    memcached_return res;
    res=memcached_behavior_set(memc, MEMCACHED_BEHAVIOR_BINARY_PROTOCOL, 1);
    if(res!=MEMCACHED_SUCCESS) { ASSERTION_VIOLATION_REP(res); INVALID_OPERATION("memcached fail"); }

    res=memcached_server_add_unix_socket(memc, "vampire_mc_socket");
    if(res!=MEMCACHED_SUCCESS) {
      USER_ERROR("Cannot connect to memcached socket: "+Int::toString(res));
    }

    resStruct=memcached_result_create(memc, &resStructObj);
    ASS_EQ(resStruct, &resStructObj);
  }
  ~StorageImpl()
  {
    CALL("Storage::StorageImpl::~StorageImpl");

    memcached_result_free(resStruct);

    memcached_free(memc);
  }

  vstring getString(const char* key, size_t keyLen, bool allowMiss=false)
  {
    CALL("Storage::StorageImpl::getString");
    ASS_L(keyLen, MEMCACHED_MAX_KEY);

    memcached_return res;
    size_t valueLen;
    char* valueChars;
    uint32_t flags;
    valueChars=memcached_get(memc, key, keyLen, &valueLen, &flags, &res);
    if(res==MEMCACHED_NOTFOUND) {
      if(allowMiss) {
	return "";
      }
      else {
	throw StorageCorruptedException();
      }
    }
    if(res!=MEMCACHED_SUCCESS) { ASSERTION_VIOLATION_REP(res); INVALID_OPERATION("memcached fail"); }
    if(!valueChars) {
      if(valueLen!=0) { ASSERTION_VIOLATION_REP(valueLen); INVALID_OPERATION("memcached fail"); }
      //empty string was stored
      return "";
    }

    vstring valueString(valueChars, valueLen);
    free(valueChars);
    return valueString;
  }

  /**
   * Return values stored under keys. For keys that do not correspond to any value,
   * empty string is given. Result strings are yielded in the order they are on the
   * stack (so that the first is the value for keys[0])
   */
  StringIterator getStrings(StringStack& keys)
  {
    CALL("Storage::StorageImpl::getStrings");

    size_t keyCnt=keys.size();

    //there seems to be a problem with the memcached_fetch in the libmemcached library,
    //so we just ask multiple times.
#if 1
    Vector<vstring>* values=Vector<vstring>::allocate(keys.size());
    for(size_t i=0;i<keyCnt;i++) {
      (*values)[i]=getString(keys[i].c_str(), keys[i].size(), true);
    }
    return pvi( Vector<vstring>::DestructiveIterator(*values) );
#else
    if(keyCnt==0) {
      return StringIterator::getEmpty();
    }

    if(keyCnt==1) {
      vstring key=keys.top();
      return pvi( getSingletonIterator( getString(key.c_str(), key.size(), true) ) );
    }

    static DArray<const char*> keyPtrs;
    static DArray<size_t> keyLengths;
    keyPtrs.ensure(keyCnt);
    keyLengths.ensure(keyCnt);
    size_t maxKeyLen=0;

    for(size_t i=0;i<keyCnt;i++) {
      keyPtrs[i]=keys[i].c_str();
      size_t keyLen=keys[i].size();
      keyLengths[i]=keyLen;
      if(keyLen>maxKeyLen) {
	maxKeyLen=keyLen;
      }
    }
    ASS_L(maxKeyLen, MEMCACHED_MAX_KEY);

    memcached_return res;

    //in the memcached header file, the second argument is of type char**,
    //however in the documentation it is of type const char * const *
    res=memcached_mget(memc, const_cast<char**>(keyPtrs.array()), keyLengths.array(), keyCnt);
    if(res!=MEMCACHED_SUCCESS) { ASSERTION_VIOLATION_REP(res); INVALID_OPERATION("memcached fail"); }

    Vector<vstring>* values=Vector<vstring>::allocate(keys.size());

    //now let's retrieve the results

    //We assume the results will most likely be retrieved in order of the keys.
    //In @b nextResIndex we store index of the first key that doesn't have its
    //value retrieved yet.
    size_t nextResIndex=0;

    static DArray<char> keyBuf;
    keyBuf.ensure(maxKeyLen+1);
    for(;;) {
      size_t keyLen, valLen;
      uint32_t flags;
      char* valueChars=memcached_fetch(memc, keyBuf.array(), &keyLen, &valLen, &flags, &res);
      if(!valueChars) {
	ASS_EQ(res, MEMCACHED_END);
	break;
      }
      if(res!=MEMCACHED_SUCCESS) { ASSERTION_VIOLATION_REP(res); INVALID_OPERATION("memcached fail"); }
      ASS_L(nextResIndex,keyCnt); //if we got a value, we must also have some key without an answer
      vstring valueStr(valueChars, valLen);
      free(valueChars);
      keyBuf[keyLen]=0;
      //now we have a null-terminated string with key starting at keyBuf.array()

      if(!strcmp(keyBuf.array(), keys[nextResIndex].c_str())) {
	RSTAT_CTR_INC("in order memcached_mget results");
	ASS_EQ((*values)[nextResIndex].size(),0);
	(*values)[nextResIndex]=valueStr;
	do {
	  nextResIndex++;
	} while(nextResIndex<keyCnt && (*values)[nextResIndex].size()!=0);
      }
      else {
	RSTAT_CTR_INC("out of order memcached_mget results");
	//let's find the position for the key we received
	size_t i=nextResIndex+1;
	//we do the check (*values)[i].size()!=0 only because it is
	//easier to check for an empty string than to compare two strings
	while(i<keyCnt && ( (*values)[i].size()!=0 || strcmp(keyBuf.array(), keys[i].c_str()) ) ) { i++; }

	//if we got a value, it's key must be there and without an answer yet
	if(i==keyCnt) { ASSERTION_VIOLATION; INVALID_OPERATION("memcached fail"); }

	(*values)[i]=valueStr;
      }
    }

#if VDEBUG
    for(size_t i=0;i<keyCnt;i++) {
      vstring fetched=(*values)[i];
      vstring check=getString(keys[i].c_str(), keys[i].size(), true);
      ASS_REP2(fetched==check, fetched.size(), check.size());
    }
#endif

    return pvi( Vector<vstring>::DestructiveIterator(*values) );
#endif
  }

  void add(const char* key, size_t keyLen, const char* val, size_t valLen)
  {
    CALL("Storage::StorageImpl::add");
    ASS_G(keyLen,0);
//    ASS(valLen<10000);
    if(keyLen>=MEMCACHED_MAX_KEY) {
      USER_ERROR("Maximum key length for memcached exceeded: "+Int::toString(keyLen));
    }
    if(valLen>=1000000) {
      USER_ERROR("Maximum value length for memcached exceeded: "+Int::toString(valLen));
    }
    ASS_REP(key[0]==THEORY_FILES || key[0]==PRED_NUM_NAME || key[0]==FUN_NUM_NAME
	|| key[0]==HAS_EMPTY_CLAUSE || valLen%storedIntMaxSize==0, (int)key[0]);

    memcached_return res;
    res=memcached_add(memc, key, keyLen, val, valLen, 0, 0);
    if(res!=MEMCACHED_SUCCESS) { ASSERTION_VIOLATION_REP(res); INVALID_OPERATION("memcached fail"); }
  }

private:
  memcached_st* memc;
  memcached_st memcObj;
  memcached_result_st* resStruct;
  memcached_result_st resStructObj;
};

Storage::Storage(bool translateSignature)
: _translateSignature(translateSignature)
{
  //equality predicate will always have the number zero
  _glob2loc.insert(make_pair(true, 0), 0);

  _impl=new StorageImpl;

  //we will be storing prefixes into a single byte
  ASS_STATIC(PREFIX_COUNT<=256);
}

Storage::~Storage()
{
  delete _impl;
}

vstring Storage::getConstKey(KeyPrefix p)
{
  CALL("Storage::getConstKey");

  char key=p;
  return _impl->getString(&key,1);
}

vstring Storage::getIntKey(KeyPrefix p, int keyNum)
{
  CALL("Storage::getIntKey");

  char keyBuf[1+storedIntMaxSize];
  keyBuf[0]=p;
  size_t keyLen=1+dumpInt(keyNum, keyBuf+1);
  return _impl->getString(keyBuf,keyLen);
}

StringIterator Storage::getIntKeyValues(KeyPrefix p, VirtualIterator<int> keyNums)
{
  CALL("Storage::getIntKeyValues");

  static StringStack keys;
  keys.reset();

  char keyBuf[1+storedIntMaxSize];
  keyBuf[0]=p;

  while(keyNums.hasNext()) {
    SymId s=keyNums.next();
    size_t keyLen=1+dumpInt(s, keyBuf+1);
    keys.push(vstring(keyBuf, keyLen));
  }

  return _impl->getStrings(keys);
}

void Storage::storeConstKey(KeyPrefix p, char* val, size_t valLen)
{
  CALL("Storage::storeConstKey");

  char key=p;
  _impl->add(&key, 1, val, valLen);
}

void Storage::storeIntKey(KeyPrefix p, int keyNum, char* val, size_t valLen)
{
  CALL("Storage::storeIntKey");

  char keyBuf[1+storedIntMaxSize];
  keyBuf[0]=p;
  size_t keyLen=1+dumpInt(keyNum, keyBuf+1);
  _impl->add(keyBuf, keyLen, val, valLen);

}


/**
 * Store integer @b num into the buffer starting at @b bufStart
 * and return number of bytes used.
 */
size_t Storage::dumpInt(int num, char* bufStart)
{
  char* pnumData=reinterpret_cast<char*>(&num);
  memcpy(bufStart, pnumData, sizeof(int));
  return sizeof(int);
}

/**
 * Read integer from buffer @b buf, store it into @b num,
 * and return number of bytes read.
 */
size_t Storage::readInt(const char* buf, int& num)
{
  char* pnumData=reinterpret_cast<char*>(&num);
  memcpy(pnumData, buf, sizeof(int));
  return sizeof(int);
}


///////////////////////////////////
// Retrieval

void Storage::getSignatureSize(int& preds, int& funs)
{
  CALL("Storage::getSignatureSize");

  vstring data=getConstKey(PRED_FUN_CNT);
  const char* ptr=data.c_str();
  ptr+=readInt(ptr,preds);
  ptr+=readInt(ptr,funs);
}

/**
 * Return list of symbols in global signature that correspond
 * to local symbols passed in @b syms. The order is not preserved,
 * and if a local symbol does not have a global counterpart, it is
 * ignored.
 *
 * Symbols are passed as pair<bool, unsigned>. If the bool is true,
 * the symbol is predicate, otherwise it is a function. The unsigned
 * part then contains number of the predicate or function in global
 * or local signature.
 */
VirtualIterator<pair<bool, unsigned> > Storage::getGlobalSymbols(Stack<pair<bool, unsigned> >& syms)
{
  CALL("Signature::getGlobalSymbols");

  StringStack queries;

  DArray<char> buf;

  Stack<pair<bool, unsigned> >::BottomFirstIterator symIt(syms);
  while(symIt.hasNext()) {
    pair<bool, unsigned> id=symIt.next();
    Signature::Symbol* sym;
    if(id.first) {
      sym=env.signature->getPredicate(id.second);
    }
    else {
      sym=env.signature->getFunction(id.second);
    }
    vstring name=Signature::key(sym->name(),sym->arity());

    size_t keyLen=1+name.size();
    buf.ensure(keyLen);
    buf[0]= id.first ? PRED_TO_NUM : FUN_TO_NUM;
    memcpy(buf.array()+1, name.c_str(), name.size());
    queries.push(vstring(buf.array(), keyLen));
  }

  StringIterator responses=_impl->getStrings(queries);

  List<pair<bool, unsigned> >* res=0;

  Stack<pair<bool, unsigned> >::BottomFirstIterator symIt2(syms);
  while(responses.hasNext()) {
    ALWAYS(symIt2.hasNext());
    vstring response=responses.next();
    pair<bool, unsigned> loc=symIt2.next();

    if(response.size()==0) {
      //the symbol has no global counterpart
      continue;
    }

    int num;
    readInt(response.c_str(), num);
    pair<bool, unsigned> globPair=make_pair(loc.first, static_cast<unsigned>(num));
    List<pair<bool, unsigned> >::push(globPair, res);
    //also mark this correspondence for the future
    _glob2loc.insert(globPair, loc.second);
  }
  NEVER(symIt2.hasNext());

  return pvi( List<pair<bool, unsigned> >::DestructiveIterator(res) );
}

/**
 * Return list of symbols in global signature that correspond
 * to local symbols passed in @b syms. The order is not preserved,
 * and if a local symbol does not have a global counterpart, it is
 * ignored.
 *
 * Symbols are passed as pair<bool, unsigned>. If the bool is true,
 * the symbol is predicate, otherwise it is a function. The unsigned
 * part then contains number of the predicate or function in global
 * or local signature.
 */
void Storage::addCorrespondingLocalSymbols(VirtualIterator<pair<bool,unsigned> > globSyms)
{
  CALL("Signature::addCorrespondingLocalSymbols");

  Stack<pair<bool,unsigned> > globStack;
  globStack.loadFromIterator(globSyms);

  //remove symbols we don't need to fetch
  Stack<pair<bool, unsigned> >::Iterator symIt0(globStack);
  while(symIt0.hasNext()) {
    pair<bool, unsigned> id=symIt0.next();
    if(_glob2loc.find(id)) {
      //if this symbol already corresponds to one in the local signature
      //there is no need to ask again
      //(and if we did, we would also have to ask for symbol name to be
      //able to pair it with the right local symbol)
      symIt0.del();
//      if(id.first) {
//      }
      continue;
    }
  }

  StringStack queries;

  //build query strings
  char keyBuf[1+storedIntMaxSize];
  Stack<pair<bool, unsigned> >::BottomFirstIterator symIt(globStack);
  while(symIt.hasNext()) {
    pair<bool, unsigned> id=symIt.next();

    keyBuf[0]= id.first ? PRED_NUM_ARITY : FUN_NUM_ARITY;
    size_t keyLen=1+dumpInt(id.second, keyBuf+1);
    queries.push(vstring(keyBuf, keyLen));
  }
  ASS_EQ(globStack.size(), queries.size());

  //now we add the unmatched global symbols into the local signature
  //with generic names
  //TODO:add name retrieval for proof output
  StringIterator responses=_impl->getStrings(queries);
  size_t index=0;
  while(responses.hasNext()) {
    vstring response=responses.next();
    pair<bool,unsigned> globSym=globStack[index++];

    int arity;
    size_t valLen=readInt(response.c_str(), arity);
    ASS_EQ(valLen, response.size());

    vstring locName=vstring("$$g")+(globSym.first ? "pred" : "fun")+Int::toString(globSym.second);
    unsigned locNum;
    bool added;
    if(globSym.first) {
      ASS_NEQ(globSym.second, 0); //equality must always correspond to equality, so we cannot add it this way
      locNum=env.signature->addPredicate(locName, arity, added);
      ASS(added);
    }
    else {
      locNum=env.signature->addFunction(locName, arity, added);
      ASS(added);
    }
    ALWAYS(_glob2loc.insert(globSym, locNum));
  }
  ASS_EQ(index, globStack.size());
}


StringList* Storage::getTheoryFileNames()
{
  char key=THEORY_FILES;
  vstring nameList=_impl->getString(&key, 1);

  const char* ptr=nameList.c_str();
  const char* afterLast=ptr+nameList.size();

  StringList* res=0;
  while(ptr!=afterLast) {
    vstring fname(ptr);
    ptr+=fname.size()+1;
    StringList::push(fname, res);
  }

  return res;
}

/**
 * Return symbols D-related to symbols in @b qsymbols whose tolerance
 * threshold is smaller or equal to @b itolerance.
 */
SymIdIterator Storage::getDRelatedSymbols(Stack<SymId>& qsymbols, unsigned itolerance)
{
  CALL("Storage::getDRelatedSymbols");
  ASS_GE(itolerance, 100);

  VirtualIterator<int> keyNums=pvi( getStaticCastIterator<int>(Stack<SymId>::Iterator(qsymbols)) );

  StringIterator values=getIntKeyValues(SYM_DSRS, keyNums);

  static Stack<SymId> rsymbols;
  rsymbols.reset();
  while(values.hasNext()) {
    vstring val=values.next();
    const char* ptr=val.c_str();
    const char* afterLast=ptr+val.size();
    while(ptr!=afterLast) {
      ASS_L(ptr, afterLast);
      int num;
      ptr+=readInt(ptr, num);
      if(num<0 && static_cast<unsigned>(-num)>itolerance) {
	//tolerance is under the tolerance threshold of further symbols
	break;
      }
      else {
	rsymbols.push(num);
      }
    }
  }
  return getPersistentIterator( Stack<SymId>::Iterator(rsymbols) );
}

/**
 * Return symbols D-related to symbols in @b qsymbols whose tolerance
 * threshold is smaller or equal to @b itolerance.
 */
VirtualIterator<unsigned> Storage::getDRelatedUnitNumbers(SymIdIterator qsymbols, unsigned itolerance)
{
  CALL("Storage::getDRelatedUnitNumbers");
  ASS_GE(itolerance, 100);

  VirtualIterator<int> keyNums=pvi( getStaticCastIterator<int>(qsymbols) );

  StringIterator values=getIntKeyValues(SYM_DURS, keyNums);

  static Stack<unsigned> unitNums;
  unitNums.reset();
  while(values.hasNext()) {
    vstring val=values.next();
    const char* ptr=val.c_str();
    const char* afterLast=ptr+val.size();
    while(ptr!=afterLast) {
      ASS_L(ptr, afterLast);
      int num;
      ptr+=readInt(ptr, num);
      if(num<0) {
	ASS_L(num, -100);
	if(static_cast<unsigned>(-num)>itolerance) {
	  //tolerance is under the tolerance threshold of further symbols
	  break;
	}
      }
      else {
	ASS_G(num, 0);
	unitNums.push(num);
      }
    }
  }
  return getPersistentIterator( Stack<unsigned>::Iterator(unitNums) );
}

VirtualIterator<unsigned> Storage::getNumbersOfUnitsWithoutSymbols()
{
  CALL("Storage::getNumbersOfUnitsWithoutSymbols");

  List<unsigned>* res=0;

  vstring val=getConstKey(UNITS_WITHOUT_SYMBOLS);
  const char* ptr=val.c_str();
  const char* afterLast=ptr+val.size();
  while(ptr!=afterLast) {
    ASS_L(ptr, afterLast);
    int num;
    ptr+=readInt(ptr, num);
    ASS_G(num,0);
    List<unsigned>::push(num, res);
  }

  return pvi( List<unsigned>::DestructiveIterator(res) );
}

UnitList* Storage::getClausesByUnitNumbers(VirtualIterator<unsigned> numIt)
{
  CALL("Storage::getClausesByUnitNumbers");
  ASS(_translateSignature);

  StringIterator clauseStrings=
      getIntKeyValues(UNIT_CNF, pvi( getStaticCastIterator<int>(numIt) ));

  Stack<Stack<int>* > dataStack;

  //split strings into clauses, convert them to numbers and record used symbol numbers
  DHSet<pair<bool, unsigned> > usedSymbols;
  int num;
  while(clauseStrings.hasNext()) {
    vstring str=clauseStrings.next();
    ASS_EQ(str.size()%storedIntMaxSize, 0);
    const char* ptr=str.c_str();
    const char* afterLast=ptr+str.size();

    if(ptr==afterLast) {
      //there is no clause in this string (see the description of @b storeCNFOfUnit )
      continue;
    }

    for(;;) {
      Stack<int>* clData=new Stack<int>;
      while(ptr!=afterLast) {
	ASS_L((void*)ptr, (void*)afterLast);
	ptr+=readInt(ptr, num);
	ASS_LE((void*)ptr, (void*)afterLast);
	if(num==0) {
	  ASS(clData->isNonEmpty()); //zero cannot be as a first thing in the clause
	  if(clData->top()==0) {
	    //second zeroes in a row means end of the clause
	    break;
	  }
	  else {
	    //one zero means end of the literal, previous number therefore stands for
	    //predicate symbol with absolute value increased by one
	    unsigned pred=abs(clData->top())-1;
	    usedSymbols.insert(make_pair(true, pred));
	  }
	}
	else {
	  if(clData->isNonEmpty() && clData->top()>0) {
	    //if positive number is not followed by zero, it is a function number increased by one
	    unsigned fun=clData->top()-1;
	    usedSymbols.insert(make_pair(false, fun));
	  }
	}
	clData->push(num);
      }
      if(ptr==afterLast && clData->isNonEmpty()) {
	ASS_NEQ(clData->top(), 0);
	//last number in a clause stands for predicate symbol with absolute value increased by one
	unsigned pred=abs(clData->top())-1;
	usedSymbols.insert(make_pair(true, pred));
	//we add zero at the end of the clause, so that every literal is followed by zero
	clData->push(0);
      }
      dataStack.push(clData);
      if(ptr==afterLast) {
	break;
      }
      ASS_L((void*)ptr, (void*)afterLast);
    }
  }

  addCorrespondingLocalSymbols(usedSymbols.iterator());

  UnitList* res=0;

  Stack<Literal*> litStack;
  Stack<TermList> termStack;

  while(dataStack.isNonEmpty()) {
    Stack<int>* clauseData=dataStack.pop();

    litStack.reset();
    termStack.reset();

    int* ptr=clauseData->begin();
    int* afterLast=clauseData->end();
    while(ptr!=afterLast) {
      int num= *(ptr++);
      ASS_NEQ(num, 0); //we deal with zeroes together with the end of the predicate symbols
      ASS_L(ptr, afterLast); //every literal is followed by a zero, so we cannot get out of the array here
      bool haveLit= *ptr==0;
      if(!haveLit) {
	TermList trm;
	if(num<0) {
	  //we have a variable
	  trm.makeVar(abs(num)-1);
	}
	else {
	  //we have a function
	  ASS_G(num,0);
	  unsigned globFunctor=num-1;
	  unsigned locFunctor=_glob2loc.get(make_pair(false, globFunctor));
	  unsigned arity=env.signature->functionArity(locFunctor);
	  ASS_GE(termStack.size(), arity);
	  trm.setTerm(Term::create(locFunctor, arity, termStack.end()-arity));
	  //remove the arguments we've just used from the stack
	  termStack.truncate(termStack.size()-arity);
	}
	termStack.push(trm);
      }
      else {
	//we have a predicate symbol, so we'll build a literal from it
	bool polarity=num>0;
	unsigned globFunctor=abs(num)-1;
	unsigned locFunctor=_glob2loc.get(make_pair(true, globFunctor));
	unsigned arity=env.signature->predicateArity(locFunctor);
	ASS_EQ(termStack.size(), arity);

	Literal* lit;
	if(locFunctor==0) {
	  ASS_EQ(arity, 2);
	  lit=Literal::createEquality(polarity, termStack[0], termStack[1]);
	}
	else {
	  lit=Literal::create(locFunctor, arity, polarity, false, termStack.begin());
	}
	litStack.push(lit);

	termStack.reset();
	ASS_EQ(*ptr, 0);
	ptr++; //advance to the start of the new literal (or the end of the clause)
      }
    }

    ASS(litStack.isNonEmpty());

    Inference* inf=new Inference0(Inference::EXTERNAL_THEORY_AXIOM);
    Clause* cl=Clause::fromIterator(LiteralStack::Iterator(litStack), Unit::AXIOM, inf);
    UnitList::push(cl, res);

    delete clauseData;
  }

  return res;
}

bool Storage::getEmptyClausePossession()
{
  CALL("Storage::storeEmptyClausePossession");

  vstring val=getConstKey(HAS_EMPTY_CLAUSE);
  return val==vstring("1");
}

///////////////////////////////////
// Storage


/**
 * Store clauses from @b cit as associated with the unit with number @b unitNumber
 *
 * There cannot be an empty clause among those being stored.
 *
 * E.g. clauses L11 \/ L12 and L21 are stored as
 *
 * (L11,0,L12,00,L21)
 *
 * Literals are stored in the postfix notation. Variables are stored as negative
 * numbers decreased by one, term symbols as positive numbers increased by one.
 * Positive occurrences of predicate symbols are stored as positive numbers increased
 * by one, negative ones as negative decreased by one.
 *
 * This is done because zero is used as a separator.
 *
 * If there is no clause associated with the unit, empty string is stored.
 */
void Storage::storeCNFOfUnit(unsigned unitNumber, ClauseIterator cit)
{
  CALL("Storage::storeCNFOfUnit");
  ASS(!_translateSignature);

  static ClauseStack cls;
  cls.reset();
  cls.loadFromIterator(cit);

  if(cls.isEmpty()) {
    storeIntKey(UNIT_CNF, unitNumber, 0, 0);
    return;
  }

  size_t bufEntries=0;
  ClauseStack::Iterator cit1(cls);
  while(cit1.hasNext()) {
    Clause* cl=cit1.next();
    ASS(cl->isClause());

    bufEntries+=cl->weight()+cl->length()+1;
  }

  size_t bufLen=bufEntries*storedIntMaxSize;
  static DArray<char> buf;
  buf.ensure(bufLen);

  char* ptr=buf.array();
  ClauseStack::Iterator cit2(cls);
  while(cit2.hasNext()) {
    Clause* cl=cit2.next();
    ASS(!cl->isEmpty());
    bool isLastClause=!cit2.hasNext();
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      Literal* lit=(*cl)[i];

      PolishSubtermIterator trmIt(lit);
      while(trmIt.hasNext()) {
	TermList t=trmIt.next();
	if(t.isVar()) {
	  ptr+=dumpInt(-t.var()-1, ptr);
	}
	else {
	  ptr+=dumpInt(t.term()->functor()+1, ptr);
	}
      }
      if(lit->isPositive()) {
	ptr+=dumpInt(lit->functor()+1, ptr);
      }
      else {
	ptr+=dumpInt(-lit->functor()-1, ptr);
      }

      if(!isLastClause || i!=(clen-1)) {
	ptr+=dumpInt(0, ptr);
      }
    }
    if(!isLastClause) {
      ptr+=dumpInt(0, ptr);
    }
  }
  size_t valLen=ptr-buf.array();
  ASS_L(valLen, bufLen);
  ASS_EQ(valLen%storedIntMaxSize, 0);

  storeIntKey(UNIT_CNF, unitNumber, buf.array(), valLen);
}

void Storage::storeUnitsWithoutSymbols(Stack<Unit*>& units)
{
  CALL("Storage::storeUnitsWithoutSymbols");

  DArray<char> buf(units.size()*storedIntMaxSize);
  char* ptr=buf.array();

  Stack<Unit*>::Iterator uit(units);
  while(uit.hasNext()) {
    ptr+=dumpInt(uit.next()->number(), ptr);
  }

  size_t valLen=ptr-buf.array();
  ASS_LE(valLen, buf.size());

  storeConstKey(UNITS_WITHOUT_SYMBOLS,  buf.array(), valLen);
}

/**
 * Store DUnitRecords for symbol @b s from stack @b durs.
 *
 * The records in stack @b s must be unique and sorted by the tolerance threshold.
 *
 * E.g.: The sequence of thresholds and units
 * (100, unit1), (120, unit2), (120, unit3), (300, unit4)
 *
 * will be stored as
 *
 * (number of unit1,-120,number of unit2,number of unit3,-300,number of unit4)
 */
void Storage::storeDURs(SymId s, Stack<DUnitRecord>& durs)
{
  CALL("Storage::storeDURs");

  static DArray<char> buf;
  buf.ensure(2*durs.size()*storedIntMaxSize);
  char* ptr=buf.array();

  unsigned prevThreshold=100;
  Stack<DUnitRecord>::BottomFirstIterator dit(durs);
  while(dit.hasNext()) {
    DUnitRecord dur=dit.next();
    if(prevThreshold!=dur.first) {
      ASS_G(dur.first, 0);
      ptr+=dumpInt(-dur.first, ptr);
    }
    ASS_G(dur.second->number(),0);
    ptr+=dumpInt(dur.second->number(), ptr);
  }
  size_t valLen=ptr-buf.array();
  ASS_LE(valLen, buf.size());

  storeIntKey(SYM_DURS, s, buf.array(), valLen);
}

/**
 * Store DSymRecords for symbol @b s from stack @b dsrs.
 *
 * The records in stack @b s must be unique and sorted by the tolerance threshold.
 *
 * E.g.: The sequence of thresholds and SymIds
 * (100, 5), (120, 2), (120, 4), (300, 1)
 *
 * will be stored as
 *
 * <5><-120><2><4><-300><1>
 */
void Storage::storeDSRs(SymId s, Stack<DSymRecord>& dsrs)
{
  CALL("Storage::storeDSRs");

  static DArray<char> buf;
  buf.ensure(2*dsrs.size()*storedIntMaxSize);

  char* ptr=buf.array();

  unsigned prevThreshold=100;
  Stack<DSymRecord>::BottomFirstIterator dit(dsrs);
  while(dit.hasNext()) {
    DSymRecord dsr=dit.next();
    if(prevThreshold!=dsr.first) {
      ASS_G(dsr.first, 100);
      ptr+=dumpInt(-dsr.first, ptr);
    }
    ASS_GE(dsr.second, 0);
    ptr+=dumpInt(dsr.second, ptr);
  }
  size_t valLen=ptr-buf.array();
  ASS_LE(valLen, buf.size());

  storeIntKey(SYM_DSRS, s, buf.array(), valLen);
}

void Storage::storeTheoryFileNames(StringStack& fnames)
{
  CALL("Storage::storeTheoryFiles");
  DArray<char> buf;
  size_t bufLen=0;

  //find out how big the value buffer should be
  StringStack::Iterator fnit1(fnames);
  while(fnit1.hasNext()) {
    bufLen+=fnit1.next().length()+1;
  }

  //fill in the value buffer
  buf.ensure(bufLen);
  char* pbuf=buf.array();
  StringStack::Iterator fnit2(fnames);
  while(fnit2.hasNext()) {
    vstring fname=fnit2.next();
    strcpy(pbuf, fname.c_str());
    pbuf+=fname.length()+1;
  }
  ASS_EQ(pbuf,buf.array()+bufLen);

  storeConstKey(THEORY_FILES, buf.array(), bufLen);
}

void Storage::storeEmptyClausePossession(bool hasEmptyClause)
{
  CALL("Storage::storeEmptyClausePossession");

  char val=hasEmptyClause ? '1' : '0';
  storeConstKey(HAS_EMPTY_CLAUSE, &val, 1);
}

void Storage::storeSignature()
{
  CALL("Storage::dumpSignature");
  ASS(!_translateSignature);

  int preds=env.signature->predicates();
  int funs=env.signature->functions();

  //store number of predicates and functions
  DArray<char> predFunCountBuf(storedIntMaxSize*2);
  char* ptr=predFunCountBuf.array();
  ptr+=dumpInt(preds, ptr);
  ptr+=dumpInt(funs, ptr);
  size_t valLength=ptr-predFunCountBuf.array();
  ASS_LE(valLength, predFunCountBuf.size());

  storeConstKey(PRED_FUN_CNT, predFunCountBuf.array(), valLength);


  for(int i=0;i<preds;i++) {
    Signature::Symbol* sym=env.signature->getPredicate(i);
    storeSymbolInfo(sym, i, false);
  }

  for(int i=0;i<funs;i++) {
    Signature::Symbol* sym=env.signature->getFunction(i);
    storeSymbolInfo(sym, i, true);
  }
}

void Storage::storeSymbolInfo(Signature::Symbol* sym, int symIndex, bool function)
{
  CALL("Storage::storeSymbolInfo");

  static DArray<char> nameBuf;
  static DArray<char> numBuf(storedIntMaxSize+1);
  static DArray<char> arityBuf(storedIntMaxSize);

  unsigned arity=sym->arity();
  vstring name=Signature::key(sym->name(), arity);

  size_t nameLen=name.length();
  nameBuf.ensure(nameLen+2);
  strcpy(nameBuf.array()+1, name.c_str());

  size_t numLen=dumpInt(symIndex, numBuf.array()+1);
  size_t arityLen=dumpInt(arity, arityBuf.array());

  //store (PRED/FUN)_TO_NUM
  nameBuf[0]=function ? FUN_TO_NUM : PRED_TO_NUM;
  _impl->add(nameBuf.array(), nameLen+1, numBuf.array()+1, numLen);

  //store (PRED/FUN)_NUM_NAME
  numBuf[0]=function ? FUN_NUM_NAME : PRED_NUM_NAME;
  _impl->add(numBuf.array(), numLen+1, nameBuf.array()+1, nameLen);

  //store (PRED/FUN)_NUM_ARITY
  numBuf[0]=function ? FUN_NUM_ARITY : PRED_NUM_ARITY;
  _impl->add(numBuf.array(), numLen+1, arityBuf.array(), arityLen);
}

}
}




