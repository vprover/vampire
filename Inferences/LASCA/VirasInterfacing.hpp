/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __Inferences_LASCA_VirasInterfacing__
#define __Inferences_LASCA_VirasInterfacing__

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Theory.hpp"
#include "Kernel/NumTraits.hpp"
#include <viras.h>


namespace Inferences {
namespace LASCA {

struct VampireVirasConfig {

  using Literals = Stack<Kernel::Literal*> const*;
  using Literal  = Kernel::Literal*;
  using Var      = Kernel::TermList;
  using Term     = Kernel::TermList;
  using Numeral  = Kernel::RationalConstantType;
  using NumTraits = Kernel::NumTraits<Numeral>;

  Numeral numeral(int i) { return Numeral(i); }
  Numeral lcm(Numeral l, Numeral r) { ASS(l.isInt() && r.isInt()); return Numeral(Kernel::IntegerConstantType::lcm(l.numerator(), r.numerator())); }
  Numeral gcd(Numeral l, Numeral r) { ASS(l.isInt() && r.isInt()); return Numeral(Kernel::IntegerConstantType::gcd(l.numerator(), r.numerator())); }

  Numeral mul(Numeral l, Numeral r) { return l * r; }
  Numeral add(Numeral l, Numeral r) { return l + r; }
  Numeral floor(Numeral t) { return t.floor(); }

  Term simpl(Term t) { return t; } // TODO

  Term term(Numeral n) { return NumTraits::constantTl(n); }
  Term term(Var v) { return v; }

  Term mul(Numeral l, Term r) { return NumTraits::mul(term(l), r); }
  Term add(Term l, Term r) { return NumTraits::add(l,r); }
  Term floor(Term t) { return NumTraits::floor(t); }

  Numeral inverse(Numeral n) { return n.inverse(); }

  bool less(Numeral l, Numeral r) { return l < r; }
  bool leq(Numeral l, Numeral r) { return l <= r; }

  std::pair<viras::PredSymbol, TermList> match_literal(Literal lit) {
    // we perform the complement of qunatifier elimination. instead of eliminating 
    // exists x. (L1 /\ L2 ...) we eliminated
    // forall x. (~L1 \/ ~L2 \/ ...)
    // thus we need to invert the literals we have
    if (lit->isEquality()) {
      auto sym = lit->isNegative() ? viras::PredSymbol::Eq 
                                   : viras::PredSymbol::Neq;
      auto l = NumTraits::isNumeral(lit->termArg(0), Numeral(0)) ? 1 : 0;
      auto r = 1 - l;
      ASS(NumTraits::isNumeral(lit->termArg(r), Numeral(0)));
      return std::make_pair(sym, NumTraits::minus(lit->termArg(l)));
    } else if (NumTraits::isGeq(lit->functor())) {
      ASS(NumTraits::isNumeral(lit->termArg(1), Numeral(0)));
      return std::make_pair(viras::PredSymbol::Gt, NumTraits::minus(lit->termArg(0)));
    } else {
      ASS_REP(NumTraits::isGreater(lit->functor()), "unexpected predicate symbol: " + lit->toString())
      ASS(NumTraits::isNumeral(lit->termArg(1), Numeral(0)));
      return std::make_pair(viras::PredSymbol::Geq, NumTraits::minus(lit->termArg(0)));
    }
  }

  viras::PredSymbol symbol_of_literal(Literal l) 
  { return match_literal(l).first; }

  Term term_of_literal(Literal l)
  { return match_literal(l).second; }

  Literal create_literal(Term t, viras::PredSymbol s) { 
    switch(s) {
      case viras::PredSymbol::Gt:  return NumTraits::geq    (true , NumTraits::minus(t), NumTraits::zero());
      case viras::PredSymbol::Geq: return NumTraits::greater(true , NumTraits::minus(t), NumTraits::zero());
      case viras::PredSymbol::Neq: return NumTraits::eq     (true , t, NumTraits::zero());
      case viras::PredSymbol::Eq:  return NumTraits::eq     (false, t, NumTraits::zero());
    }
  }

  Numeral num(Numeral l) { return Numeral(l.numerator()); }

  Numeral den(Numeral l) { return Numeral(l.denominator()); }

  size_t literals_size(Literals const& l) { return l->size(); }
  Literal literals_get(Literals const& l, size_t idx) { return (*l)[idx]; }

  template<class IfVar, class IfOne, class IfMul, class IfAdd, class IfFloor>
  auto matchTerm(Term t, 
      IfVar   if_var, 
      IfOne   if_one, 
      IfMul   if_mul, 
      IfAdd   if_add, 
      IfFloor if_floor) -> decltype(if_one()) {
    return NumTraits::ifNumeral(t, [&](auto n) { return n == Numeral(1) ? if_one() : if_mul(n, term(numeral(1))); })
     .orElse([&]() { return NumTraits::ifAdd(t, [&](auto l, auto r) { return if_add(l, r); }); })
     .orElse([&]() { return NumTraits::ifMinus(t, [&](auto t) { return if_mul(numeral(-1), t); }); })
     .orElse([&]() { return NumTraits::ifMul(t, [&](auto l, auto r) { 
                           return NumTraits::ifNumeral(l, [&](auto k) { return if_mul(k, r); });
                     }).flatten(); })
     .orElse([&]() { return NumTraits::ifDiv(t, [&](auto l, auto r) { 
                           return NumTraits::ifNumeral(r, [&](auto k) { return if_mul(k.inverse(), l); });
                     }).flatten(); })
     .orElse([&]() { return NumTraits::ifFloor(t, [&](auto t) { return if_floor(t); }); })
     .orElse([&]() { return if_var(t); });
  }
#ifdef VDEBUG
  Var test_var(const char* name) {
    auto f = env.signature->addFunction(name, 0);
    env.signature->getFunction(f)->setType(Kernel::OperatorType::getFunctionType({}, NumTraits::sort()));
    return TermList(Kernel::Term::createConstant(f));                                                          
  }
#endif // VDEBUG
};


} // namespace LASCA 
} // namespace Inferences 

#endif // __Inferences_LASCA_VirasInterfacing__
