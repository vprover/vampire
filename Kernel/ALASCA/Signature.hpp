/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __ALASCA_Signature__
#define __ALASCA_Signature__

namespace Kernel {

// TODO rename
template<class NumTraits, class F>
Option<std::invoke_result_t<F, AlascaPredicate, TermList, unsigned>> ifAlascaLiteral(Literal* lit, F f) {
  // TODO assert normalized
  if (NumTraits::isGreater(lit->functor())) {
    ASS(lit->termArg(1) == NumTraits::constantTl(0))
    return some(f(AlascaPredicate::GREATER   , lit->termArg(0), 0));
  }
  if (NumTraits::isGeq(lit->functor())    ) {
    ASS(lit->termArg(1) == NumTraits::constantTl(0))
    return some(f(AlascaPredicate::GREATER_EQ, lit->termArg(0), 0));
  }
  if (lit->isEquality() && SortHelper::getEqualityArgumentSort(lit) == NumTraits::sort()) {
    auto i = 0;
    if (auto n = NumTraits::tryNumeral(lit->termArg(0))) {
      if (*n == 0) {
        i++;
      }
    }
    return some(f(lit->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ, lit->termArg(i), i));
  }
  return {};
}

// TODO rename
template<class NumTraits, class T, class F>
auto ifNumMul(T term, F f) {
  return NumTraits::ifMul(term, [&](auto l, auto r) {
      ASS(!NumTraits::isNumeral(r))
      return NumTraits::ifNumeral(l, [&](auto l) { return f(l, r, 1); });
  }).flatten()
  .orElse([&](){
      return NumTraits::ifMinus(term, [&](auto t) { return  f(NumTraits::constant(-1), t, 0); });
      });
}

// TODO rename
template<class NumTraits, class T>
auto isNumMul(T term) 
{ return ifNumMul<NumTraits>(term, [](auto...) { return 0; }).isSome(); }

// TODO rename
template<class NumTraits, class T>
auto isAlascaLiteral(T term) 
{ return ifAlascaLiteral<NumTraits>(term, [](auto...) { return 0; }).isSome(); }

// TODO rename
template<class NumTraits, class T>
auto isUninterpreted(T t) 
{ return !NumTraits::isFloor(t) && !NumTraits::isAdd(t) && !isNumMul<NumTraits>(t); }


} // namespace Kernel


#endif // __ALASCA_Signature__
