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
 * @file FlexibleTail.hpp
 *
 * Utility class for derived classes that need a flexible array member at the end, like
 *
 * struct Term {
 *   unsigned arity;
 *   TermList args[]; // zero or more TermLists
 * };
 *
 * which are intended as one allocation:
 *
 * arity | <maybe padding> | arg[0] | ... | arg[arity - 1]
 */

#ifndef __FlexibleTail__
#define __FlexibleTail__

#include <cstddef>

namespace Lib {

/*
 * Inherit from this class to get a flexibleTail(), e.g.
 * struct SATClause : public FlexibleTail<SATClause, SATLiteral> { ... }
 * NB CRTP parameter.
 *
 * You will need to implement operator new/operator delete in a manner of your choosing.
 * Call allocationRequired() to know how many bytes you need.
 *
 * The resulting object will be laid out as follows:
 * | derived | <maybe padding> | arg[0] | ... | arg[arity - 1]|
 * ^ this
 *           ^ this + sizeof(Derived)
 *                             ^ flexibleTail()
 *                                                            ^ flexibleTail() + arity * sizeof(TermList)
 */
template<typename Derived, typename T>
struct FlexibleTail {
  FlexibleTail() = default;

  // copying/moving such an object is in principle possible but tricky
  // - could implement if ever needed
  FlexibleTail(const FlexibleTail &) = delete;
  FlexibleTail(FlexibleTail &&) = delete;

  // how far is the tail from `this`, in bytes?
  constexpr static size_t tailOffset() {
    size_t derived = sizeof(Derived);
    // may need some padding
    if(derived % alignof(T))
      derived += alignof(T) - (derived % alignof(T));
    return derived;
  }

  // number of bytes required for Derived with a tail of `length`
  constexpr static size_t bytesRequiredFor(unsigned length) {
    return tailOffset() + length * sizeof(T);
  }

  /*
   * pointer to tail array if tailLength() is non-zero, nullptr otherwise
   *
   * creating (not dereferencing) an invalid pointer is UB,
   * so we cannot return a sensible pointer for the zero-length case */
  T *flexibleTail() const {
    if(!((Derived *)this)->tailLength())
      return nullptr;

    return (T *)((char *)this + tailOffset());
  }
};

}

#endif
