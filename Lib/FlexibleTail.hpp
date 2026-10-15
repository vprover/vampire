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
 * Call bytesRequiredFor(n) to know how many bytes you need to allocate.
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

  // copying/moving such an object is possible but tricky
  // - could relax this if ever needed
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

  // number of bytes required for `Derived` with a tail of `length`
  constexpr static size_t bytesRequiredFor(unsigned length) {
    /* note that we include the padding even when length == 0
     * this means that the flexibleTail() pointer remains valid (I hope!)
     * since creating a one-past-the-end pointer is OK */
    return tailOffset() + length * sizeof(T);
  }

  // compute pointer to tail array
  T *flexibleTail() {
    // hazard: in some situations me != this, e.g. multiple inheritance
    // thanks to Pietro Pellegrino for pointing this out
    auto me = static_cast<Derived *>(this);
    return (T *)((char *)me + tailOffset());
  }

  const T *flexibleTail() const {
    // hazard: in some situations me != this, e.g. multiple inheritance
    // thanks to Pietro Pellegrino for pointing this out
    auto me = static_cast<const Derived *>(this);
    return (const T *)((char *)me + tailOffset());
  }
};

}

#endif
