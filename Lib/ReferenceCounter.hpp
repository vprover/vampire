/**
 * @file ReferenceCounter.hpp
 * Defines class ReferenceCounter.
 */


#ifndef __ReferenceCounter__
#define __ReferenceCounter__

#include "Allocator.hpp"
#include "../Debug/Assertion.hpp"

namespace Lib {

class ReferenceCounter
{
public:
  ReferenceCounter()
  {
    _counter=ALLOC_KNOWN(sizeof(Counter), "ReferenceCounter::Counter");
    *_counter=1;
  }
  ReferenceCounter(const ReferenceCounter& rc)
  {
    _counter=rc._counter;
    inc();
  }
  ReferenceCounter& operator=(const ReferenceCounter& rc)
  {
    dec();
    _counter=rc._counter;
    inc();
  }
  bool isLast()
  {
    return !*_counter;
  }
private:
  inline void inc()
  {
    (*_counter)++;
    ASS_NEQ(*_counter,0);
  }
  inline void dec()
  {
    ASS_NEQ(*_counter,0);
    (*_counter)--;
    if(!*_counter) {
      DEALLOC_KNOWN(_counter,sizeof(Counter),"ReferenceCounter::Counter");
    }
  }

  typedef size_t Counter;
  Counter* _counter;
};

};

#endif /* __ReferenceCounter__ */
