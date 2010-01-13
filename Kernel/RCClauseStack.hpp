/**
 * @file RCClauseStack.hpp
 * Defines class RCClauseStack.
 */

#ifndef __RCClauseStack__
#define __RCClauseStack__

#include "../Forwards.hpp"

#include "../Lib/Stack.hpp"

#include "../Kernel/Clause.hpp"

namespace Kernel {

using namespace Lib;

/**
 * A clause stack that enforces reference counting on inserted clauses
 */
class RCClauseStack {
public:
  void push(Clause* cl)
  {
    CALL("RCClauseStack::push");

    cl->incRefCnt();
    _s.push(cl);
  }

  Clause* pop()
  {
    CALL("RCClauseStack::pop");

    Clause* cl=_s.pop();
    cl->decRefCnt();
    return cl;
  }

  /**
   * Pop a clause from the stack without decreasing the reference counter
   * (this will be up to the caller)
   */
  Clause* popWithoutDec()
  {
    CALL("RCClauseStack::popWithoutDec");

    return _s.pop();;
  }

  bool isEmpty() { return _s.isEmpty(); }
  bool isNonEmpty() { return _s.isNonEmpty(); }

  void reset()
  {
    while(isNonEmpty()) {
      pop();
    }
  }

  class Iterator
  {
  public:
    DECL_ELEMENT_TYPE(Clause*);

    Iterator(RCClauseStack& s) : _inner(s._s) {}

    bool hasNext() { return _inner.hasNext(); }
    Clause* next() { return _inner.next(); }

  private:
    ClauseStack::Iterator _inner;
  };

private:
  ClauseStack _s;
};

}

#endif // __RCClauseStack__
