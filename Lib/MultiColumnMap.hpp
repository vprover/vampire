/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MultiColumnMap.hpp
 * Defines class MultiColumnMap.
 *
 * Currently not used anywhere and does not compile in VS2008
 */


#ifndef __MultiColumnMap__
#define __MultiColumnMap__

#include "Allocator.hpp"
#include "BitUtils.hpp"
#include "DHMap.hpp"

namespace Lib {

template<typename Key>
class MultiColumnMap
{
public:
  MultiColumnMap() : _entryCount(0), _entryDataSize(0) {}

  ~MultiColumnMap()
  {
    //TODO:Implement destruction of items stored in the map
    typename DHMap<Key,char*>::Iterator dit(_data);
    while(dit.hasNext()) {
      char* entry=dit.next();
      DEALLOC_KNOWN(entry, getEntrySize(), "MultiColumnMap");
    }
  }

  template<typename T>
  class AccessObject;

  template<typename T>
  AccessObject<T> addColumn()
  {
    //we cannot add columns once we've inserted an entry.
    ASS_EQ(_data.size(),0);

    AccessObject<T> res(this, _entryCount, _entryDataSize);
    _entryCount++;
    _entryDataSize+=sizeof(T);
    return res;
  }

  template<typename T>
  class AccessObject
  {
  public:
    bool getOrCreate(Key k,T*& ptr)
    {
      char* entry=_obj->getEntry(k);
      bool res=!BitUtils::getBitValue(entry+_entryDataSize, _index);
      ptr=entry+_offset;
      return res;
    }
  private:
    AccessObject(MultiColumnMap* obj, unsigned index, unsigned offset)
    : _obj(obj), _index(index), _offset(offset) {}

    MultiColumnMap* _obj;
    unsigned _index;
    unsigned _offset;

    friend class MultiColumnMap;
  };

private:
  char* getEntry(Key k)
  {
    char** ppdata;
    if(_data.getValuePtr(k, ppdata)) {
      *ppdata=ALLOC_KNOWN(getEntrySize(), "MultiColumnMap");
      BitUtils::zeroMemory(*ppdata+_entryDataSize, getOccupancyBitsSize());
    }
    return *ppdata;
  }

  inline
  unsigned getOccupancyBitsSize()
  { return ((_entryCount-1)/8+1); }

  inline
  unsigned getEntrySize()
  { return _entryDataSize + getOccupancyBitsSize(); }

  unsigned _entryCount;
  unsigned _entryDataSize;
  DHMap<Key,char*> _data;
};

};

#endif /* __MultiColumnMap__ */
