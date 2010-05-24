/**
 * @file Storage.cpp
 * Implements class Storage.
 */

#include <malloc.h>
#include <string.h>
#include <libmemcached/memcached.h>

#include "Debug/Assertion.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"

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
    ASS_L(keyLen, MEMCACHED_MAX_KEY);

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

/**
 * Store integer @b num into the buffer starting at @b bufStart
 * and return number of bytes used.
 */
size_t Storage::storeInt(int num, char* bufStart)
{
  char* pnumData=reinterpret_cast<char*>(&num);
  memcpy(bufStart, pnumData, sizeof(int));
  return sizeof(int);
}

void Storage::storeTheoryFileNames(StringStack& fnames)
{
  CALL("Storage::storeTheoryFiles");
  DArray<char> buf;
  size_t bufLen=0;

  //find out how big the value buffer should be
  StringStack::Iterator fnit1(fnames);
  while(fnit1.hasNext()) {
    bufLen=fnit1.next().length()+1;
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

  //store the value
  char key=THEORY_FILES;
  _impl->add(&key,1,buf.array(), bufLen);
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


void Storage::dumpSignature()
{
  CALL("Storage::dumpSignature");
  ASS(!_translateSignature);

  int preds=env.signature->predicates();
  for(int i=0;i<preds;i++) {
    Signature::Symbol* sym=env.signature->getPredicate(i);
    storeSymbolInfo(sym, i, false);
  }

  int funs=env.signature->functions();
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

  size_t numLen=storeInt(symIndex, numBuf.array()+1);
  size_t arityLen=storeInt(arity, arityBuf.array());

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




