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
#include "Stack.hpp"

namespace Lib
{

class Recycler {
public:
  template<typename T>
  static void release(T* obj)
  {
    ASS(obj);
    List<T*>::push(obj, getStore<T>());
    obj->reset();
  }
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
  static void get(Stack<T>*& result)
  {
    List<Stack<T>*>*& store=getStore<Stack<T> >();
    if(store) {
      result=List<Stack<T>*>::pop(store);
    } else {
      result=new Stack<T>(8);
    }
  }
private:
  template<typename T>
  static List<T*>*& getStore()
  {
    static List<T*>* store=0;
    return store;
  }
};

};

#endif /*__Recycler__*/
