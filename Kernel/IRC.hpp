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
 * @file IRC.cpp
 * Defines all functionality shared among the components of the inequality resolution calculus.
 *
 */



#ifndef __IRC__
#define __IRC__

#include "Kernel/Formula.hpp"
#include "Lib/Int.hpp"
#include "Forwards.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/LaKbo.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Signature.hpp" 
#include "SortHelper.hpp"
#include "Sorts.hpp"
#include "TermIterators.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "NumTraits.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Coproduct.hpp"
#include <algorithm>
#include <utility>
#include <type_traits>
#include <functional>
#include "Lib/Hash.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Option.hpp"
#include "Debug/Tracer.hpp"
#include "Kernel/Polynomial.hpp"
#include "Kernel/BottomUpEvaluation.hpp"
#include "Kernel/BottomUpEvaluation/TermList.hpp"
#include "Kernel/BottomUpEvaluation/PolyNf.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Kernel/PolynomialNormalizer.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)


namespace Kernel {
  using Inferences::PolynomialEvaluation;
   
  enum class IrcPredicate {
    EQ,
    NEQ,
    GREATER,
    GREATER_EQ,
  };

  /** returns true iff the predicate is > or >= */
  bool isInequality(IrcPredicate const& self);

  std::ostream& operator<<(std::ostream& out, IrcPredicate const& self);

  /** 
   * Represents an inequality literal normalized for the rule InequalityResolution.
   * this means it is a literal of the form
   *      term == 0 or term != 0 or term >= 0 or term > 0 (for Reals and Rationals)
   * or   term == 0 or term != 0              or term > 0 (for Integers)
   */
  template<class NumTraits>
  class IrcLiteral {
    Perfect<Polynom<NumTraits>> _term;
    IrcPredicate _symbol;

  public:
    IrcLiteral(Perfect<Polynom<NumTraits>> term, IrcPredicate symbol) 
      : _term(term), _symbol(symbol) 
    { _term->integrity(); }

    friend class InequalityNormalizer;

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return *_term; }

    IrcPredicate symbol() const
    { return _symbol; }

    friend std::ostream& operator<<(std::ostream& out, IrcLiteral const& self) 
    { return out << self._term << " " << self._symbol << " 0"; }

    Literal* denormalize() const
    {
      auto l = term().denormalize();
      auto r = NumTraits::zero();
      switch(symbol()) {
        case IrcPredicate::EQ:  return NumTraits::eq(true, l, r);
        case IrcPredicate::NEQ: return NumTraits::eq(false, l, r);
        case IrcPredicate::GREATER: return NumTraits::greater(true, l, r);
        case IrcPredicate::GREATER_EQ: return NumTraits::geq(true, l, r);
      }
      ASSERTION_VIOLATION
    }

    bool isInequality() const
    { return Kernel::isInequality(symbol()); }
  };
  using AnyIrcLiteral = Coproduct< IrcLiteral< IntTraits>
                                 , IrcLiteral< RatTraits>
                                 , IrcLiteral<RealTraits>
                                 >;
  
  /** 
   * Represents an inequality literal normalized for the rule InequalityResolution.
   * this means it is a literal of the form
   *      term > 0 or term >= 0 (for Reals and Rationals)
   * or   term > 0              (for Integers)
   */
  template<class NumTraits>
  class InequalityLiteral {
    IrcLiteral<NumTraits> _self;

  public:
    InequalityLiteral(Perfect<Polynom<NumTraits>> term, bool strict) 
      : InequalityLiteral(IrcLiteral<NumTraits>(term, strict ? IrcPredicate::GREATER : IrcPredicate::GREATER_EQ))
    {}

    IrcLiteral<NumTraits> const& inner() const { return _self; }

    explicit InequalityLiteral(IrcLiteral<NumTraits> self) 
      : _self(std::move(self)) 
    { ASS(self.isInequality()) }

    /* returns the lhs of the inequality lhs >= 0 (or lhs > 0) */
    Polynom<NumTraits> const& term() const
    { return _self.term(); }

    /* 
     * returns whether this is a strict inequality (i.e. >), 
     * or a non-strict one (i.e. >=) 
     * */
    bool strict() const
    { return _self.symbol() == IrcPredicate::GREATER; }

    friend std::ostream& operator<<(std::ostream& out, InequalityLiteral const& self) 
    { return out << self._self; }

    Literal* denormalize() const
    { return _self.denormalize(); }
  };

  class InequalityNormalizer {
    // Map<Literal*, Option<InequalityLiteral>> _normalized;
    PolynomialEvaluation _eval;

  public:
    PolynomialEvaluation& evaluator() { return _eval; }
    InequalityNormalizer(PolynomialEvaluation eval) 
      : _eval(std::move(eval)) {  }

    template<class NumTraits> Option<MaybeOverflow<IrcLiteral<NumTraits>>> normalizeIrc(Literal* lit) const;

    Option<MaybeOverflow<AnyIrcLiteral>> normalize(Literal* lit) const;

    template<class NumTraits> Option<MaybeOverflow<InequalityLiteral<NumTraits>>> normalizeIneq(Literal* lit) const;

    Literal* normalizeLiteral(Literal* lit) const;
    bool isNormalized(Clause* cl)  const;
  };

  struct IrcState;

  template<class TermOrLit> 
  auto applySubst(RobSubstitution const& subst, TermOrLit t, int varBank) { return subst.apply(t, varBank);  }

  template<class TermOrLit> 
  auto applySubst(Indexing::ResultSubstitution& subst, TermOrLit t, int varBank) { return subst.applyTo(t, varBank);  }


  struct UwaResult {
    RobSubstitution sigma;
    Stack<UnificationConstraint> cnst;
    UwaResult(UwaResult&&) = default;
    UwaResult& operator=(UwaResult&&) = default;

    template<class Subst>
    static auto cnstLiterals(Subst& sigma, Stack<UnificationConstraint> const& cnst)
    {
      return iterTraits(cnst.iterFifo())
        .map([&](auto c){
          auto toTerm = [&](pair<TermList, unsigned> const& weirdConstraintPair) -> TermList
                        { return applySubst(sigma, weirdConstraintPair.first, weirdConstraintPair.second); };
          auto sort = SortHelper::getResultSort(c.first.first.term());
          // lσ != rσ
          return Literal::createEquality(false, toTerm(c.first), toTerm(c.second), sort);
        });
    }

    auto cnstLiterals() const
    { return cnstLiterals(sigma, cnst); }

    friend std::ostream& operator<<(std::ostream& out, UwaResult const& self)
    { 
      out << "⟨" << self.sigma << ", [";
      auto iter = self.cnstLiterals();
      if (iter.hasNext()) {
        out << *iter.next();
        while (iter.hasNext())
          out << " \\/ " << *iter.next();
      }
      return out << "]⟩"; 
    }
  private:
    UwaResult() : sigma(), cnst() {  }
    friend struct IrcState;
  };

  struct IrcState {
    InequalityNormalizer normalizer;
    Ordering* const ordering;
    Shell::Options::UnificationWithAbstraction const uwa;

    template<class NumTraits> Stack<Monom<NumTraits>> maxAtomicTerms(IrcLiteral<NumTraits>const& lit);

    Option<UwaResult> unify(TermList lhs, TermList rhs) const;
    Option<AnyIrcLiteral> normalize(Literal*);
    PolyNf normalize(TypedTermList);
  };

#if VDEBUG
  shared_ptr<IrcState> testIrcState(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ONE_INTERP
    );
#endif

}

////////////////////////////////////////////////////////////////////////////
// impl InequalityLiteral
/////////////////////////////
  
namespace Kernel {

template<class NumTraits>
Option<MaybeOverflow<InequalityLiteral<NumTraits>>> InequalityNormalizer::normalizeIneq(Literal* lit) const
{
  using Opt = Option<MaybeOverflow<InequalityLiteral<NumTraits>>>;
  return normalizeIrc<NumTraits>(lit)
    .andThen([](auto overflown) {
      if (overflown.value.isInequality()) {
        return Opt(overflown.map([](auto lit) { return InequalityLiteral<NumTraits>(std::move(lit)); }));
      } else {
        return Opt();
      }
    });
}

template<class NumTraits>
Option<MaybeOverflow<IrcLiteral<NumTraits>>> InequalityNormalizer::normalizeIrc(Literal* lit) const
{
  // auto normalizeEqSign = [](Perfect<Polynom<NumTraits>> const& t) -> Perfect<Polynom<NumTraits>>{
  //   auto pol = 0;
  //   for (auto s : t->iterSummands()) {
  //     if (s.numeral.isPositive()) {
  //       pol++;
  //     } else {
  //       ASS(s.numeral.isNegative())
  //       pol--;
  //     }
  //   }
  //   if (pol >= 0) {
  //     return t;
  //   } else {
  //     return perfect(Polynom<NumTraits>(t->iterSummands()
  //           .map([](auto s) { return Monom<NumTraits>(-s.numeral, s.factor); })))
  //   }
  // }
  CALL("InequalityLiteral<NumTraits>::fromLiteral(Literal*)")
  DEBUG("in: ", *lit, " (", NumTraits::name(), ")")

  auto impl = [&]() {

    constexpr bool isInt = std::is_same<NumTraits, IntTraits>::value;

    using Opt = Option<MaybeOverflow<IrcLiteral<NumTraits>>>;

    auto f = lit->functor();
    if (!theory->isInterpretedPredicate(f))
      return Opt();

    auto itp = theory->interpretPredicate(f);


    IrcPredicate pred;
    TermList l, r; // <- we rewrite to l < r or l <= r
    switch(itp) {
      case Interpretation::EQUAL:
        if (SortHelper::getEqualityArgumentSort(lit) != NumTraits::sort()) 
          return Opt();
        l = *lit->nthArgument(0);
        r = *lit->nthArgument(1);
        pred = lit->isPositive() ? IrcPredicate::EQ : IrcPredicate::NEQ;
        break;

      case NumTraits::leqI: /* l <= r */
        l = *lit->nthArgument(0);
        r = *lit->nthArgument(1);
        pred = IrcPredicate::GREATER_EQ;
        break;

      case NumTraits::geqI: /* l >= r ==> r <= l */
        l = *lit->nthArgument(1);
        r = *lit->nthArgument(0);
        pred = IrcPredicate::GREATER_EQ;
        break;

      case NumTraits::lessI: /* l < r */
        l = *lit->nthArgument(0);
        r = *lit->nthArgument(1);
        pred = IrcPredicate::GREATER;
        break;

      case NumTraits::greaterI: /* l > r ==> r < l */
        l = *lit->nthArgument(1);
        r = *lit->nthArgument(0);
        pred = IrcPredicate::GREATER;
        break;

      default: 
        return Opt();
    }

    if (lit->isNegative() && isInequality(pred)) {
      // ~(l >= r) <==> (r < l)
      std::swap(l, r);
      pred = pred == IrcPredicate::GREATER ? IrcPredicate::GREATER_EQ : IrcPredicate::GREATER;
    }

    if (isInt && pred == IrcPredicate::GREATER_EQ) {
      /* l <= r ==> l < r + 1 */
      r = NumTraits::add(r, NumTraits::one());
      pred = IrcPredicate::GREATER;
    }

    /* l < r ==> r > l ==> r - l > 0 */
    auto t = NumTraits::add(r, NumTraits::minus(l));

    ASS(!isInt || pred != IrcPredicate::GREATER_EQ)
    auto tt = TypedTermList(t, NumTraits::sort());
    auto norm = Kernel::normalizeTerm(tt);
    auto simpl = _eval.evaluate(norm);
    auto simplValue = simpl.value || norm;
    simplValue.integrity();
    auto out = IrcLiteral<NumTraits>(simplValue.wrapPoly<NumTraits>(), pred);
    return Opt(maybeOverflow(std::move(out), simpl.overflowOccurred));
  };
  auto out = impl();
  DEBUG("out: ", out);
  return out;
}


////////////////////////////////////////////////////////////////////////////
// impl IrcState
/////////////////////////////




template<class NumTraits>
Stack<Monom<NumTraits>> IrcState::maxAtomicTerms(IrcLiteral<NumTraits>const& lit)
{
  using Monom = Monom<NumTraits>;
  Stack<Monom> max(lit.term().nSummands()); // TODO not sure whether this size allocation brings an advantage
  auto monoms = lit.term().iterSummands().template collect<Stack>();
  for (unsigned i = 0; i < monoms.size(); i++) {
    auto isMax = true;
    for (unsigned j = 0; j < monoms.size(); j++) {
      auto cmp = ordering->compare(
          monoms[i].factors->denormalize(), 
          monoms[j].factors->denormalize());
      if (cmp == Ordering::LESS) {
          isMax = false;
          break;
      } else if(cmp == Ordering::EQUAL || cmp == Ordering::INCOMPARABLE || Ordering::GREATER) {
        /* ok */
      } else {
        ASSERTION_VIOLATION_REP(cmp)
      }
    }
    if (isMax && monoms[i].factors->tryVar().isNone())  // TODO we don't wanna skip varibles in the future
    // if (isMax)  // TODO we don't wanna skip varibles in the future
      max.push(monoms[i]);
  }
  return max;
}

} // namespace Kernel

#undef DEBUG
#endif // __IRC__

