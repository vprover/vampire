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
#include "Lib/Stack.hpp"
#include "Lib/Vector.hpp"

#include "Kernel/Clause.hpp"
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

  string getString(const char* key, size_t keyLen)
  {
    CALL("Storage::StorageImpl::add");
    ASS_L(keyLen, MEMCACHED_MAX_KEY);

    memcached_return res;
    size_t valueLen;
    char* valueChars;
    uint32_t flags;
    valueChars=memcached_get(memc, key, keyLen, &valueLen, &flags, &res);
    if(!valueChars) {
      throw StorageCorruptedException();
    }
    if(res!=MEMCACHED_SUCCESS) { ASSERTION_VIOLATION_REP(res); INVALID_OPERATION("memcached fail"); }

    string valueString(valueChars, valueLen);
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
    CALL("Storage::StorageImpl::add");

    size_t keyCnt=keys.size();

    static DArray<const char*> keyPtrs;
    static DArray<size_t> keyLengths;
    keyPtrs.ensure(keyCnt);
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

    Vector<string>* values=Vector<string>::allocate(keys.size());

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
      string valueStr(valueChars, valLen);
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

    return pvi( Vector<string>::DestructiveIterator(*values) );
  }

  void add(const char* key, size_t keyLen, const char* val, size_t valLen)
  {
    CALL("Storage::StorageImpl::add");
    ASS(valLen<10000);
    if(keyLen>=MEMCACHED_MAX_KEY) {
      USER_ERROR("Maximum key length for memcached exceeded: "+Int::toString(keyLen));
    }
    if(valLen>=1000000) {
      USER_ERROR("Maximum value length for memcached exceeded: "+Int::toString(valLen));
    }

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
  _impl=new StorageImpl;

  //we will be storing prefixes into a single byte
  ASS_STATIC(PREFIX_COUNT<=256);
}

Storage::~Storage()
{
  delete _impl;
}

string Storage::getConstKey(KeyPrefix p)
{
  CALL("Storage::getConstKey");

  char key=p;
  return _impl->getString(&key,1);
}

string Storage::getIntKey(KeyPrefix p, int keyNum)
{
  CALL("Storage::getIntKey");

  char keyBuf[1+storedIntMaxSize];
  keyBuf[0]=p;
  size_t keyLen=1+dumpInt(keyNum, keyBuf+1);
  return _impl->getString(keyBuf,keyLen);
}

StringIterator Storage::getIntKeyValues(KeyPrefix p, VirtualIterator<int> keyNums)
{
  static StringStack keys;
  keys.reset();

  char keyBuf[1+storedIntMaxSize];
  keyBuf[0]=SYM_DSRS;

  while(keyNums.hasNext()) {
    SymId s=keyNums.next();
    size_t keyLen=1+dumpInt(s, keyBuf+1);
    keys.push(string(keyBuf, keyLen));
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

  string data=getConstKey(PRED_FUN_CNT);
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

  Stack<pair<bool, unsigned> >::Iterator symIt(syms);
  while(symIt.hasNext()) {
    pair<bool, unsigned> id=symIt.next();
    Signature::Symbol* sym;
    if(id.first) {
      sym=env.signature->getPredicate(id.second);
    }
    else {
      sym=env.signature->getFunction(id.second);
    }
    string name=Signature::key(sym->name(),sym->arity());

    size_t keyLen=1+name.size();
    buf.ensure(keyLen);
    buf[0]= id.first ? PRED_TO_NUM : FUN_TO_NUM;
    memcpy(buf.array()+1, name.c_str(), name.size());
    queries.push(string(buf.array(), keyLen));
  }

  StringIterator responses=_impl->getStrings(queries);

  List<pair<bool, unsigned> >* res=0;

  Stack<pair<bool, unsigned> >::Iterator symIt2(syms);
  while(responses.hasNext()) {
    ALWAYS(symIt2.hasNext());
    string response=responses.next();
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
void Storage::getLocalSymbols(VirtualIterator<pair<bool,unsigned> > globSyms, DHMap<pair<bool,unsigned>, unsigned>& resMap)
{
  CALL("Signature::getGlobalSymbols");

  Stack<pair<bool,unsigned> > globStack;
  globStack.loadFromIterator(globSyms);

  StringStack queries;

  char keyBuf[1+storedIntMaxSize];

  Stack<pair<bool, unsigned> >::Iterator symIt(globStack);
  while(symIt.hasNext()) {
    pair<bool, unsigned> id=symIt.next();
    unsigned storedLoc;
    if(_glob2loc.find(id, storedLoc)) {
      resMap.insert(id, storedLoc);
      symIt.del();
      continue;
    }
    Signature::Symbol* sym;
    if(id.first) {
      sym=env.signature->getPredicate(id.second);
    }
    else {
      sym=env.signature->getFunction(id.second);
    }
    string name=Signature::key(sym->name(),sym->arity());

    keyBuf[0]= id.first ? PRED_NUM_ARITY : FUN_NUM_ARITY;
    size_t keyLen=1+dumpInt(id.second, keyBuf+1);
    queries.push(string(keyBuf, keyLen));
  }
  ASS_EQ(globStack.size(), queries.size());

//  StringIterator responses=_impl->getStrings(queries);
//
//  List<pair<bool, unsigned> >* res=0;
//
//  Stack<pair<bool, unsigned> >::Iterator symIt2(syms);
//  while(responses.hasNext()) {
//    ALWAYS(symIt2.hasNext());
//    string response=responses.next();
//    pair<bool, unsigned> loc=symIt2.next();
//
//    if(response.size()==0) {
//      //the symbol has no global counterpart
//      continue;
//    }
//
//    int num;
//    readInt(response.c_str(), num);
//    List<pair<bool, unsigned> >::push(make_pair(loc.first, static_cast<unsigned>(num)), res);
//  }
//  NEVER(symIt2.hasNext());
//
//  return pvi( List<pair<bool, unsigned> >::DestructiveIterator(res) );
}


StringList* Storage::getTheoryFileNames()
{
  char key=THEORY_FILES;
  string nameList=_impl->getString(&key, 1);

  const char* ptr=nameList.c_str();
  const char* afterLast=ptr+nameList.size();

  StringList* res=0;
  while(ptr!=afterLast) {
    string fname(ptr);
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
    string val=values.next();
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

  StringIterator values=getIntKeyValues(SYM_DSRS, keyNums);

  static Stack<unsigned> unitNums;
  unitNums.reset();
  while(values.hasNext()) {
    string val=values.next();
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

  string val=getConstKey(UNITS_WITHOUT_SYMBOLS);
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
  CALL("Storage::getDRelatedUnitNumbers");
  ASS(_translateSignature);

  StringStack clauseStrings;
  clauseStrings.loadFromIterator(getIntKeyValues(UNIT_CNF,
      pvi( getStaticCastIterator<int>(numIt) )));

  Stack<Stack<int>* > dataStack;

  //split strings into clauses, convert them to numbers and record used symbol numbers
  DHSet<pair<bool, unsigned> > usedSymbols;
  int num;
  StringStack::Iterator csit(clauseStrings);
  while(csit.hasNext()) {
    string str=csit.next();
    const char* ptr=str.c_str();
    const char* afterLast=ptr+str.size();

    if(ptr!=afterLast) {
      readInt(ptr, num);
      if(num==0) {
  	//there is no clause in this string (see the description of @b storeCNFOfUnit )
	ASS_LE(str.size(), storedIntMaxSize);
  	continue;
      }
    }

    //ptr is still at the first character (we haven't shifted it)
    for(;;) {
      Stack<int>* clData=new Stack<int>;
      while(ptr!=afterLast) {
	ptr+=readInt(ptr, num);
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
      if(clData->isNonEmpty()) {
	ASS_NEQ(clData->top(), 0);
	//last number in a clause stands for predicate symbol with absolute value increased by one
	unsigned pred=abs(clData->top())-1;
	usedSymbols.insert(make_pair(true, pred));
      }
      //we add zero at the end of the clause, so that every literal is followed by zero
      clData->push(0);

      dataStack.push(clData);
    }
  }

  NOT_IMPLEMENTED;

  UnitList* res=0;


  return res;
}


///////////////////////////////////
// Storage


/**
 * Store clauses from @b cit as associated with the unit with number @b unitNumber
 *
 * E.g. clauses L11 \/ L12 and L21 are stored as
 *
 * <L11>0<L12>00<L21>
 *
 * Literals are stored in the postfix notation. Variables are stored as negative
 * numbers decreased by one, term symbols as positive numbers increased by one.
 * Positive occurences of predicate symbols are stored as positive numbers increased
 * by one, negative ones as negative decreased by one.
 *
 * This is done because zero is used as a separator.
 *
 * If there is no clause associated with the unit, one zero is stored (storing empty
 * sequence would mean an empty clause).
 */
void Storage::storeCNFOfUnit(unsigned unitNumber, ClauseIterator cit)
{
  CALL("Storage::storeCNFOfUnit");
  ASS(!_translateSignature);

  static ClauseStack cls;
  cls.reset();
  cls.loadFromIterator(cit);

  if(cls.isEmpty()) {
    char val=0;
    storeIntKey(UNIT_CNF, unitNumber, &val, 1);
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
	*(ptr++)=0;
      }
    }
    if(!isLastClause) {
      *(ptr++)=0;
    }
  }
  size_t valLen=ptr-buf.array();
  ASS_L(valLen, bufLen);

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
 * <number of unit1><-120><number of unit2><number of unit3><-300><number of unit4>
 */
void Storage::storeDURs(SymId s, Stack<DUnitRecord>& durs)
{
  CALL("Storage::storeDURs");

  static DArray<char> buf;
  buf.ensure(2*durs.size()*storedIntMaxSize);
  char* ptr=buf.array();

  unsigned prevThreshold=100;
  Stack<DUnitRecord>::Iterator dit(durs);
  while(dit.hasNext()) {
    DUnitRecord dur=dit.next();
    if(prevThreshold!=dur.first) {
      ASS_G(dur.first, 0);
      ptr+=dumpInt(-dur.first, ptr);
    }
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
  Stack<DSymRecord>::Iterator dit(dsrs);
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
    string fname=fnit2.next();
    strcpy(pbuf, fname.c_str());
    pbuf+=fname.length()+1;
  }
  ASS_EQ(pbuf,buf.array()+bufLen);

  storeConstKey(THEORY_FILES, buf.array(), bufLen);
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
  string name=Signature::key(sym->name(), arity);

  size_t nameLen=name.length();
  nameBuf.ensure(nameLen+1);
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




