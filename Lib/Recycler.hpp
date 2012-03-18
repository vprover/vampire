/**
 * @file Recycler.hpp
 * Defines class SmartPtr for smart pointers
 *
 * @since 08/05/2007 Manchester
 */

#ifndef __Recycler__
#define __Recycler__

#include "Forwards.hpp"

#include "Stack.hpp"
#include "DArray.hpp"

namespace Lib
{
using namespace Indexing;

class Recycler {
public:
  template<typename T>
  static void get(T*& result)
  {
    Stack<T*>& store=getStore<T>();
    if(store.isNonEmpty()) {
      result=store.pop();
    } else {
      result=new T();
    }
  }

  template<typename T>
  static void get(DArray<T>*& result)
  {
    Stack<DArray<T>*>& store=getStore<DArray<T> >();
    if(store.isNonEmpty()) {
      result=store.pop();
    } else {
      result=new DArray<T>(64);
      result->ensure(0);
    }
  }


  template<typename T>
  static void release(T* obj)
  {
    ASS(obj);

    Stack<T*>& store=getStore<T>();

    store.push(obj);
  }


private:

  template<typename T>
  static Stack<T*>& getStore() throw()
  {
    static Stack<T*> store(4);
    return store;
  }
};

};

#endif /*__Recycler__*/
