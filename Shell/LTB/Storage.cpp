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
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"

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
    ASS_EQ(res,MEMCACHED_SUCCESS);

    res=memcached_server_add_unix_socket(memc, "vampire_mc_socket");
    if(res!=MEMCACHED_SUCCESS) {
      USER_ERROR("Cannot connect to memcached socket.");
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
    ASS_EQ(res,MEMCACHED_SUCCESS);

    string valueString(valueChars, valueLen);
    free(valueChars);
    return valueString;
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
    ASS_EQ(res,MEMCACHED_SUCCESS);
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
 * Store clauses from @b cit as associated with the unit with number @b unitNumber
 *
 * E.g. clauses L11 \/ L12 and L21 are stored as
 *
 * <L11>0<L12>00<L21>
 *
 * Literals are stored in the postfix notation. Variables are stored as negative
 * numbers decreased by one (as we have only one zero), term symbols as positive
 * numbers increased by one. Positive occurences of predicate symbols are stored
 * as positive numbers increased by one, negative ones as negative decreased by one.
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
  string name=sym->name();

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




