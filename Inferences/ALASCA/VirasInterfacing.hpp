/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __Inferences_ALASCA_VirasInterfacing__
#define __Inferences_ALASCA_VirasInterfacing__

#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/Term.hpp"
#define VIRAS_DEBUG_LEVEL 0
#define VIRAS_ASSERT(...) ASS(__VA_ARGS__)
#define VIRAS_OUTPUT(...) DBG(__VA_ARGS__)
#include <viras.h>


namespace Inferences {
namespace ALASCA {


// TODO more num traits?

template<class NumTraits>
struct VampireVirasConfig 
{
  struct VarWrapper : public TermList {
    VarWrapper() : TermList() {}
    VarWrapper(TermList t) : TermList(t) {}
  };

  using ASig     = Kernel::AlascaSignature<NumTraits>;
  using Literals = Stack<Kernel::Literal*> const*;
  using Literal  = Kernel::Literal*;
  using Var      = VarWrapper;
  using Term     = Kernel::TermList;
  using Numeral  = typename ASig::ConstantType;

  void output_literals(std::ostream& out, Stack<Kernel::Literal*> const* const& self) { out << Kernel::Output::interleaved(", ", arrayIter(*self).map([](auto x) -> Kernel::Literal& { return *x; })); }
  void output_literal(std::ostream& out, Kernel::Literal* const& self) { out << *self; }
  void output_var(std::ostream& out, VarWrapper const& self) { out << self; }
  void output_term(std::ostream& out, Kernel::TermList const& self) { out << self; }
  void output_numeral(std::ostream& out, Numeral const& self) { out << self; }

  Numeral numeral(int i) { return Numeral(i); }
  Numeral lcm(Numeral l, Numeral r) { ASS(l.isInt() && r.isInt()); return Numeral(l.numerator().lcm(r.numerator())); }
  Numeral gcd(Numeral l, Numeral r) { ASS(l.isInt() && r.isInt()); return Numeral(l.numerator().gcd(r.numerator())); }

  Numeral mul(Numeral l, Numeral r) { return l * r; }
  Numeral add(Numeral l, Numeral r) { return l + r; }
  Numeral floor(Numeral t) { return Numeral(t.floor()); }

  Term term(Numeral n) { return ASig::numeralTl(n); }
  Term term(Var v) { return v; }

  Term mul(Numeral l, Term r) { return ASig::linMul(l, r); }
  Term add(Term l, Term r) { return ASig::add(l,r); }
  Term floor(Term t) { return ASig::floor(t); }

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
      auto l = ASig::isNumeral(lit->termArg(0), Numeral(0)) ? 1 : 0;
      ASS(ASig::isNumeral(lit->termArg(1 - l), Numeral(0)));
      return std::make_pair(sym, ASig::minus(lit->termArg(l)));
    } else if (ASig::isGeq(lit->functor())) {
      ASS(ASig::isNumeral(lit->termArg(1), Numeral(0)));
      return std::make_pair(viras::PredSymbol::Gt, ASig::minus(lit->termArg(0)));
    } else {
      ASS_REP(ASig::isGreater(lit->functor()), "unexpected predicate symbol: " + lit->toString())
      ASS(ASig::isNumeral(lit->termArg(1), Numeral(0)));
      return std::make_pair(viras::PredSymbol::Geq, ASig::minus(lit->termArg(0)));
    }
  }

  viras::PredSymbol symbol_of_literal(Literal l) 
  { return match_literal(l).first; }

  Term term_of_literal(Literal l)
  { return match_literal(l).second; }

  Literal create_literal(Term t, viras::PredSymbol s) { 
    switch(s) {
      case viras::PredSymbol::Gt:  return ASig::geq    (true , ASig::minus(t), ASig::zero());
      case viras::PredSymbol::Geq: return ASig::greater(true , ASig::minus(t), ASig::zero());
      case viras::PredSymbol::Neq: return ASig::eq     (true , t, ASig::zero());
      case viras::PredSymbol::Eq:  return ASig::eq     (false, t, ASig::zero());
    }
    ASSERTION_VIOLATION
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

    return ASig::ifOne(t, std::move(if_one))
     .orElse([&]() { return ASig::ifAdd(t, [&](auto l, auto r) { return if_add(l, r); }); })
     .orElse([&]() { return ASig::ifMinus(t, [&](auto t) { return if_mul(numeral(-1), t); }); })
     .orElse([&]() { return ASig::ifLinMul(t, std::move(if_mul)); })
     .orElse([&]() { return ASig::tryNumeral(t).toOwned()
                                   .map([&](auto n) { return if_mul(n, ASig::one()); }); })
     .orElse([&]() { return ASig::ifFloor(t, [&](auto t) { return if_floor(t); }); })
     .orElse([&]() { return ASig::ifDiv(t, [&](auto l, auto r) { 
                           return ASig::ifNumeral(r, [&](auto k) { return 
                                someIf(k != 0, [&](){ return if_mul(k.inverse(), l); }); }).flatten();
                               }).flatten();
                   })
     .orElse([&]() { return if_var(VarWrapper(t)); });

  }

#ifdef VDEBUG
  Var test_var(const char* name) {
    auto f = env.signature->addFunction(name, 0);
    env.signature->getFunction(f)->setType(Kernel::OperatorType::getFunctionType({}, ASig::sort()));
    return VarWrapper(TermList(Kernel::Term::createConstant(f)));
  }
#endif // VDEBUG

};

} // namespace ALASCA 
} // namespace Inferences 

#endif // __Inferences_ALASCA_VirasInterfacing__
