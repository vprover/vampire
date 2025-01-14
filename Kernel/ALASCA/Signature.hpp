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

#include "Kernel/NumTraits.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"

namespace Kernel {

enum class AlascaPredicate {
  EQ,
  NEQ,
  GREATER,
  GREATER_EQ,
};

/** returns true iff the predicate is > or >= */
inline bool isInequality(AlascaPredicate const& self) 
{
  switch(self) {
    case AlascaPredicate::EQ: 
    case AlascaPredicate::NEQ: return false;
    case AlascaPredicate::GREATER: 
    case AlascaPredicate::GREATER_EQ: return true;
  }
  ASSERTION_VIOLATION
}

template<class NumTraits>
Literal* createLiteral(AlascaPredicate self, TermList t)
{
  auto zero = NumTraits::constantTl(NumTraits::constant(0));
  switch(self) {
    case AlascaPredicate::EQ: return NumTraits::eq(true, t, zero);
    case AlascaPredicate::NEQ: return NumTraits::eq(false, t, zero);
    case AlascaPredicate::GREATER: return NumTraits::greater(true, t, zero);
    case AlascaPredicate::GREATER_EQ: return NumTraits::geq(true, t, zero);
  }
  ASSERTION_VIOLATION
}
bool isIsInt(AlascaPredicate const& self);

inline std::ostream& operator<<(std::ostream& out, AlascaPredicate const& self)
{ 
  switch(self) {
    case AlascaPredicate::EQ: return out << "==";
    case AlascaPredicate::NEQ: return out << "!=";
    case AlascaPredicate::GREATER: return out << ">";
    case AlascaPredicate::GREATER_EQ: return out << ">=";
  } 
  ASSERTION_VIOLATION
}

#define ALASCA_MULTI_NUMERAL 1

template<class NumTraits> 
struct AlascaSignature : public NumTraits {
  using Numeral = typename NumTraits::ConstantType;
  static Option<Numeral> oneN;
  static Option<TermList> oneT;
  static Option<TermList> sortT;
  static Option<TermList> zeroT;

  template<class T>
  static Option<Numeral const&> tryNumeral(T t) {
#if ALASCA_MULTI_NUMERAL
    return NumTraits::tryNumeral(t);
#else 
    if (t == AlascaSignature::one()) {
      return Option<Numeral const&>(oneN.unwrapOrInit([&]() { return NumTraits::constant(1); }));
    } else {
      return NumTraits::ifLinMul(t, [](auto& c, auto t) {
          return someIf(t == NumTraits::one(), [&]() -> auto& { return c; });
      }).flatten();
    }
#endif
  }
  /* numerals might b complex terms */
  static Option<Numeral const&> tryNumeral(unsigned t) = delete; 

  template<class T> static void numeralF(T) = delete;
  template<class T> static void constantTl(T) = delete;

  static auto addF() { return NumTraits::addF(); }
  static auto minusF() { return NumTraits::linMulF(Numeral(-1)); }

  static TermList minus(TermList t) { return TermList(Term::create(minusF(), {t})); }

  template<class F>
  static decltype(auto) ifLinMul(Term const* t, F fun)
  { return NumTraits::ifLinMul(t, std::move(fun)); }

  template<class F>
  static decltype(auto) ifLinMul(TermList t, F fun)
  { return someIf(t.isTerm(), [&]() { return ifLinMul(t.term(), std::move(fun)); }).flatten(); }

  template<class T, class F, class P>
  static decltype(auto) ifLinMulWithPath(T t, P& path, F fun) 
  { 
    path.push(0);
    decltype(auto) out = NumTraits::ifLinMul(t, std::move(fun));
    path.pop();
    return out; 
  }

  template<class T>
  static auto isUninterpreted(T t) 
  { return !NumTraits::isFloor(t) && !NumTraits::isAdd(t) && !NumTraits::isLinMul(t) && !AlascaSignature::isOne(t); }

  static auto isUninterpreted(TermList t) 
  { return !isVar(t) && isUninterpreted(t.term()); }

  static auto isNumeral(TermList t, Numeral n) { return AlascaSignature::tryNumeral(t) == Option<Numeral const&>(n); }
  static auto isNumeral(TermList t) { return AlascaSignature::tryNumeral(t).isSome(); }

  static auto isVar(TermList t) { return t.isVar(); }
  static auto isVar(Term* t) { return false; }

  // TODO check if any of the uses should include isOne as atomic
  // TODO check if we could skip the LinMul part
  // TODO what about ⌊x⌋
  template<class T>
  static auto isAtomic(T t) 
  { return !isVar(t) && !AlascaSignature::isAdd(t) && !AlascaSignature::isLinMul(t); }

  template<class Iter>
  static TermList sum(Iter iter) {
    return iterTraits(std::move(iter))
      .fold([](auto l, auto r) { return AlascaSignature::add(l, r); })
      .unwrapOrElse([&]() { return AlascaSignature::zero(); });
  }

  template<class T>
  static TermList linMul(int c, T t) { return AlascaSignature::linMul(Numeral(c), t); }

  template<class T>
  static TermList linMul(Numeral const& c, T t) 
  { return c == 1 ? TermList(t) : NumTraits::linMul(c, t); }

  template<class... Args> static TermList ifMul(Args...)  = delete;
  template<class... Args> static TermList isMul(Args...)  = delete;
  template<class... Args> static TermList mul(Args...) = delete;
  template<class... Args> static TermList mulF(Args...)  = delete;
  template<class... Args> static TermList tryMul(Args...)  = delete;

  static TermList const& zero() { return zeroT.unwrapOrInit([&]() { return AlascaSignature::numeralTl(0); }); }
  static TermList const& one() { return oneT.unwrapOrInit([&]() { return NumTraits::one(); }); }
  static TermList const& sort() { return sortT.unwrapOrInit([&]() { return NumTraits::sort(); }); }

  static bool isZero(TermList t) { return AlascaSignature::zero() == t; }

  static bool isOne(unsigned f) { return AlascaSignature::one().term()->functor() == f; }
  static bool isOne(TermList t) { return AlascaSignature::one() == t; }
  static bool isOne(Term* t) { return AlascaSignature::one() == TermList(t); }

  template<class T, class F>
  static auto ifOne(T term, F fun) { return someIf(AlascaSignature::isOne(term), std::move(fun)); }

  static Kernel::TermList numeralTl(int c) 
  { return numeralTl(NumTraits::constant(c)); }

  static Kernel::TermList numeralTl(typename NumTraits::ConstantType const& c) 
#if ALASCA_MULTI_NUMERAL
  { return NumTraits::constantTl(c); }
#else
  { return c == 1 ? AlascaSignature::one() : TermList(NumTraits::linMul(c, AlascaSignature::one())); }
#endif //ALASCA_MULTI_NUMERAL


  template<class F>
  static Option<std::invoke_result_t<F, AlascaPredicate, TermList, unsigned>> ifAlascaLiteralWithPath(Literal* lit, F f) {
    if (NumTraits::isGreater(lit->functor())) {
      ASS_EQ(lit->termArg(1),  AlascaSignature::numeralTl(0))
      return some(f(AlascaPredicate::GREATER, lit->termArg(0), 0));
    }
    if (NumTraits::isGeq(lit->functor())    ) {
      ASS_EQ(lit->termArg(1),  AlascaSignature::numeralTl(0))
      return some(f(AlascaPredicate::GREATER_EQ, lit->termArg(0), 0));
    }
    if (lit->isEquality() && lit->eqArgSort() == NumTraits::sort()) {
      auto i = 0;
      if (auto n = AlascaSignature::tryNumeral(lit->termArg(0))) {
        if (*n == 0) {
          i++;
        }
      }
      ASS_EQ(lit->termArg(1 - i),  AlascaSignature::numeralTl(0))
      return some(f(lit->isPositive() ? AlascaPredicate::EQ : AlascaPredicate::NEQ, lit->termArg(i), i));
    }
    return {};
  }


  template<class F>
  static Option<std::invoke_result_t<F, AlascaPredicate, TermList>> ifAlascaLiteral(Literal* lit, F f) 
  { return ifAlascaLiteral(lit, [&](auto p, auto t, auto i) { return f(p,t); }); }

  static auto isAlascaLiteral(Literal* lit) 
  { return AlascaSignature::ifAlascaLiteralWithPath(lit, [](auto...) { return 0; }).isSome(); }
};

template<class NumTraits>
AlascaSignature<NumTraits> asig(NumTraits n) 
{ return AlascaSignature<NumTraits> {}; }

template<typename NumTraits> Option<typename AlascaSignature<NumTraits>::Numeral> AlascaSignature<NumTraits>::oneN;
template<typename NumTraits> Option<TermList> AlascaSignature<NumTraits>::oneT;
template<typename NumTraits> Option<TermList> AlascaSignature<NumTraits>::sortT;
template<typename NumTraits> Option<TermList> AlascaSignature<NumTraits>::zeroT;


} // namespace Kernel


#endif // __ALASCA_Signature__
