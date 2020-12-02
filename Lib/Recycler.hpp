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

  /*
  * A Stack which deletes its elements at the end.
  */
  template<typename T> 
  struct OwnedPtrStack : public Stack<T*>
  {  
    inline
    explicit OwnedPtrStack (size_t initialCapacity=0)
      : Stack<T*> (initialCapacity) { }
  
    inline ~OwnedPtrStack() { 
      while (this->isNonEmpty())
        delete (this->pop());
     }
  };

  template<typename T>
  static Stack<T*>& getStore() throw()
  {
    static OwnedPtrStack<T> store(4);
    return store;
  }
};

};

#endif /*__Recycler__*/
