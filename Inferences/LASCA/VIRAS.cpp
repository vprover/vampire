/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "VIRAS.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/LASCA.hpp"
#include "Kernel/NumTraits.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Option.hpp"

using namespace Kernel;
using namespace Inferences;
using namespace LASCA;
using namespace Lib;

#include <viras.h>

struct VampireVirasConfig {

  using Literals = Stack<Literal*> const*;
  using Literal  = Kernel::Literal*;
  using Var      = Kernel::TermList;
  using Term     = Kernel::TermList;
  using Numeral  = RationalConstantType;
  using NumTraits = ::NumTraits<Numeral>;

  Numeral numeral(int i) { return Numeral(i); }
  Numeral lcm(Numeral l, Numeral r) { ASS(l.isInt() && r.isInt()); return Numeral(IntegerConstantType::lcm(l.numerator(), r.numerator())); }
  Numeral gcd(Numeral l, Numeral r) { ASS(l.isInt() && r.isInt()); return Numeral(IntegerConstantType::gcd(l.numerator(), r.numerator())); }

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
     .orElse([&]() { return NumTraits::ifFloor(t, [&](auto t) { return if_floor(t); }); })
     .orElse([&]() { return if_var(t); });
  }
};

template<class VirasIter>
class IntoVampireIter {
  VirasIter _iter;
  Option<std::optional<viras::iter::value_type<VirasIter>>> _next;
public:
  IntoVampireIter(VirasIter iter) : _iter(std::move(iter)), _next() {}

  DECL_ELEMENT_TYPE(viras::iter::value_type<VirasIter>);
  void loadNext() { 
    if (_next.isNone()) {
      _next = some(_iter.next());
    }
  }

  bool hasNext() {
    loadNext();
    return bool(*_next);
  }

  viras::iter::value_type<VirasIter> next() {
    loadNext();
    return std::move(*_next.take().unwrap());
  }
};

template<class VirasIter>
auto intoVampireIter(VirasIter i) 
{ return iterTraits(IntoVampireIter<VirasIter>(std::move(i))); }

struct Void {};
template<class F>
void traverseLiraVars(TermList self, F f) {
  VampireVirasConfig{}.
    matchTerm(self, 
      /* var v */ [&](auto y) { f(y); return Void {}; }, 
      /* numeral 1 */ [&]() { return Void {}; }, 
      /* k * t */ [&](auto k, auto t)  { traverseLiraVars(t, f); return Void {}; }, 
      /* l + r */ [&](auto l, auto r)  { 
        traverseLiraVars(l, f);
        traverseLiraVars(r, f);
        return Void {}; 
      }, 
      /* floor */ [&](auto t) { traverseLiraVars(t, f); return Void {}; }
      );
}

SimplifyingGeneratingInference::ClauseGenerationResult VirasQuantifierElimination::generateSimplify(Clause* premise) {
  using NumTraits = RatTraits;
  auto viras = viras::viras(viras::simplifyingConfig(VampireVirasConfig{}));
  Recycled<DHSet<unsigned>> shieldedVars;
  Recycled<DHSet<unsigned>> candidateVars;
  Recycled<Stack<Literal*>> toElim;
  Recycled<Stack<Literal*>> otherLits;
  auto noteShielded = [&](Term* t) {
    VariableIterator vars(t);
    while (vars.hasNext()) 
     shieldedVars->insert(vars.next().var());
  };

  Recycled<DHSet<unsigned>> topLevelVars;
  for (auto l : premise->iterLits()) {
    Option<LascaLiteral<RatTraits>> norm = _shared->renormalize(l)
      .flatMap([](auto l) { return l.template as<LascaLiteral<NumTraits>>().toOwned(); })
      .filter([](auto l) { switch(l.symbol()) {
          case LascaPredicate::EQ:
          case LascaPredicate::NEQ:
          case LascaPredicate::GREATER:
          case LascaPredicate::GREATER_EQ: return true;
          case LascaPredicate::IS_INT_POS:
          case LascaPredicate::IS_INT_NEG: return false;
          }});

    if (norm.isNone()) {
      otherLits->push(l);
      noteShielded(l);
    } else {
      toElim->push(l);
      traverseLiraVars(norm->term().denormalize(), 
          [&](TermList t) {
            if (t.isVar()) {
              candidateVars->insert(t.var());
            } else {
              noteShielded(t.term());
            }
          });
    }
  }

  auto unshielded = iterTraits(candidateVars->iterator())
    .filter([&](auto x) { return !shieldedVars->contains(x); })
    .tryNext();

  if (unshielded.isNone()) {
    return ClauseGenerationResult {
      .clauses = VirtualIterator<Clause*>::getEmpty(),
      .premiseRedundant = false,
    };
  } else {
    auto var = TermList::var(*unshielded);
    auto analysed = std::make_unique<std::vector<typename decltype(viras)::LiraLiteral>>(viras.analyse(&*toElim, var));
    return ClauseGenerationResult {
      .clauses = pvi(
          intoVampireIter(viras.quantifier_elimination(var, *analysed))
            .map([premise, analysed = std::move(analysed), otherLits = std::move(otherLits)](auto litIter) { 
              return Clause::fromIterator(
                  concatIters(
                    intoVampireIter(litIter),
                    otherLits->iter()
                    ), 
                  Inference(SimplifyingInference1(InferenceRule::LASCA_VIRAS_QE, premise)));
            })
          )
        ,
      .premiseRedundant = true,
    };
  }
}

