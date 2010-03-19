/**
 * @file Recycler.hpp
 * Defines class SmartPtr for smart pointers
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __Recycler__
#define __Recycler__

#include "../Forwards.hpp"

#include "List.hpp"
#include "DArray.hpp"

namespace Lib
{
using namespace Indexing;

class Recycler {
public:
  template<typename T>
  static void get(T*& result)
  {
    List<T*>*& store=getStore<T>();
    if(store) {
      result=List<T*>::pop(store);
    } else {
      result=new T();
    }
  }

  template<typename T>
  static void get(DArray<T>*& result)
  {
    List<DArray<T>*>*& store=getStore<DArray<T> >();
    if(store) {
      result=List<DArray<T>*>::pop(store);
    } else {
      result=new DArray<T>(64);
    }
  }


  template<typename T>
  static void release(T* obj)
  {
    ASS(obj);

    putIntoStoreOrDelete<T>(obj);
  }


private:

  template<typename T>
  static void putIntoStoreOrDelete(T* obj)
  {
    List<T*>* itm=0;
    List<T*>*& store=getStore<T>();
    try {
      itm=new List<T*>(obj, store);
    } catch(MemoryLimitExceededException e) {
      if(!Exception::isThrownDuringExceptionHandling()) {
	throw;
      }
    }

    if(itm) {
      store=itm;
    } else {
      delete obj;
    }
  }

  template<typename T>
  static List<T*>*& getStore() throw()
  {
    static List<T*>* store=0;
    return store;
  }
};

};

#endif /*__Recycler__*/
