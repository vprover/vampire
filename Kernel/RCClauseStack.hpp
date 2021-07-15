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
 * @file RCClauseStack.hpp
 * Defines class RCClauseStack.
 */

#ifndef __RCClauseStack__
#define __RCClauseStack__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"

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

  void pushWithoutInc(Clause* cl)
  {
    CALL("RCClauseStack::push");

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

    return _s.pop();
  }

  bool isEmpty() { return _s.isEmpty(); }
  bool isNonEmpty() { return _s.isNonEmpty(); }

  void reset()
  {
    while(isNonEmpty()) {
      pop();
    }
  }

  size_t size() const
  {
    return _s.size();
  }

  class Iterator
  {
  public:
    DECL_ELEMENT_TYPE(Clause*);

    Iterator(const RCClauseStack& s) : _inner(s._s) {}

    bool hasNext() { return _inner.hasNext(); }
    Clause* next() { return _inner.next(); }

  private:
    ClauseStack::ConstIterator _inner;
  };

  class DelIterator
  {
  public:
    DECL_ELEMENT_TYPE(Clause*);

    DelIterator(RCClauseStack& s) : _inner(s._s), curr(nullptr) {}

    bool hasNext() { return _inner.hasNext(); }
    Clause* next() {
      curr = _inner.next();
      return curr;
    }
    void del() {
      _inner.del();
      curr->decRefCnt();
    }
    void replace(Clause* replacement) {
      _inner.replace(replacement);
      replacement->incRefCnt();
      curr->decRefCnt();
      curr = replacement;
    }

  private:
    ClauseStack::DelIterator _inner;
    Clause* curr;
  };

  bool find(Clause* cl) const
  {
    CALL("RCClauseStack::find");

    Iterator it(const_cast<RCClauseStack&>(*this));
    while(it.hasNext()) {
      if(it.next()==cl) {
	return true;
      }
    }
    return false;
  }
  
private:
  ClauseStack _s;
};

}

#endif // __RCClauseStack__
