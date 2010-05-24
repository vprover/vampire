/**
 * @file Storage.cpp
 * Implements class Storage.
 */

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
    memc=memcached_create(0);

    memcached_return res;
    res=memcached_server_add_unix_socket(memc, "vampire_mc_socket");
    if(res!=MEMCACHED_SUCCESS) {
      USER_ERROR("Cannot connect to memcached socket.");
    }
  }
  ~StorageImpl()
  {
    CALL("Storage::StorageImpl::~StorageImpl");

    memcached_free(memc);
  }

  void add(const char* key, size_t keyLen, const char* val, size_t valLen)
  {
    CALL("Storage::StorageImpl::add");

    memcached_return res;
    res=memcached_add(memc, key, keyLen, val, valLen, 0, 0);
    ASS(res==MEMCACHED_SUCCESS);
  }

private:
  memcached_st *memc;
};

Storage::Storage(bool translateSignature)
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

void Storage::dumpSignature()
{
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




