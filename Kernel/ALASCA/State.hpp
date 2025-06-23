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
 * Defines functions and structres that are shared by all ALASCA inference rules in order to select literals, terms, etc.
 */

#ifndef __ALASCA_State__
#define __ALASCA_State__

#include "Debug/Assertion.hpp"
#include "Kernel/ALASCA/Selection.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include <utility>

namespace Kernel {
  struct AlascaState 
  {
    USE_ALLOCATOR(AlascaState);

    // TODO get rid of this
    static std::shared_ptr<AlascaState> globalState;

  private:
    AlascaState(
          std::shared_ptr<InequalityNormalizer> normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction uwa,
          bool fixedPointIteration,
          AlascaSelector sel
        )
      : _normalizer(std::move(normalizer))
      , ordering(std::move(ordering))
      , uwa(uwa) 
      , uwaFixedPointIteration(fixedPointIteration)
      , selector(std::move(sel))
    {}

  public:
    std::shared_ptr<InequalityNormalizer> _normalizer;
    Ordering* const ordering;
    Shell::Options::UnificationWithAbstraction uwa;
    bool const uwaFixedPointIteration;
    AlascaSelector selector;

    InequalityNormalizer& norm() const { return *_normalizer; }
    std::shared_ptr<InequalityNormalizer> normalizerPtr() const { return _normalizer; }

    Shell::Options::UnificationWithAbstraction uwaMode() const { return uwa; }


    static std::shared_ptr<AlascaState> create(
          std::shared_ptr<InequalityNormalizer> normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction const uwa,
          bool const fixedPointIteration,
          AlascaSelector sel
        ) 
    {
      globalState = Lib::make_shared(AlascaState(std::move(normalizer), ordering, uwa, fixedPointIteration, std::move(sel)));
      return globalState;
    }

    bool isAtomic(Term* t) const
    { return forAllNumTraits([&](auto n) { return asig(n).isAtomic(t); }); }

    bool isAtomic(TermList t) const { return t.isTerm() && isAtomic(t.term()); }

    // TODO 2 depreacte these, they should be included into  post-unification checks
    template<class LitOrTerm0, class LitOrTerm1>
    bool greater(LitOrTerm0 lhs, LitOrTerm1 rhs)
    { return ordering->compare(lhs, rhs) == Ordering::Result::GREATER; }

    template<class LitOrTerm0, class LitOrTerm1>
    bool notLess(LitOrTerm0 lhs, LitOrTerm1 rhs)
    { return OrderingUtils::notLess(ordering->compare(lhs, rhs)); }

    template<class LitOrTerm0, class LitOrTerm1>
    bool notLeq(LitOrTerm0 lhs, LitOrTerm1 rhs)
    { return OrderingUtils::notLeq(ordering->compare(lhs, rhs)); }

    template<class NumTraits>
    auto maxSummandIndices(AlascaTermItp<NumTraits> const& term, SelectionCriterion selection)
    {
        // TODO optimize less denormalization
        auto monomAt = [=](auto i) 
             { return term.summandAt(i).atom(); }; 

        return iterTraits(OrderingUtils::maxElems(
                  term.nSummands(),
                  [=](unsigned l, unsigned r) 
                  { return ordering->compare(monomAt(l), monomAt(r)); },
                  [=](unsigned i)
                  { return monomAt(i); },
                  selection))
                 .filter([=](auto& i) { return selection == SelectionCriterion::NOT_LEQ ? !term.summandAt(i).isNumeral()
                                            : selection == SelectionCriterion::NOT_LESS ? !term.summandAt(i).isNumeral() // <- TODO re-think about this case. i think we stay complete in this case but I can't say 100% for sure.
                                            : true; });
    }

    bool subtermEqModT(TypedTermList sub, TypedTermList sup)
    {
      ASS(isAtomic(sub))
      return norm().normalize(sup).toTerm()
        .containsSubterm(norm().normalize(sub).toTerm());
    }

    auto isUninterpreted(Literal* l) const 
    { return !l->isEquality() && norm().tryNormalizeInterpreted(l).isNone(); }

    bool interpretedFunction(TermList t) 
    { return t.isTerm() && interpretedFunction(t.term()); }

    bool interpretedFunction(Term* t) 
    { return forAnyNumTraits([&](auto numTraits) -> bool {
            return theory->isInterpretedFunction(t, numTraits.addI)
                || theory->isInterpretedFunction(t, numTraits.minusI)
                || theory->isInterpretedConstant(t)
                || (theory->isInterpretedFunction(t, numTraits.mulI)
                    && theory->isInterpretedConstant(t->termArg(0)));
      }); }

    // TODO move to AlascaUtils
    static bool interpretedPred(Literal* t) {
      auto f = t->functor();
      return t->isEquality()
        || forAnyNumTraits([&](auto numTraits) -> bool {
            return numTraits.isGeq(f)
               ||  numTraits.isGreater(f);
      });
    }

    bool isUninterpretedEquality(Literal* t) {
      return t->isEquality()
        && !forAnyNumTraits([&](auto numTraits) -> bool {
            return SortHelper::getEqualityArgumentSort(t) == numTraits.sort();
      });
    }

    auto selected(Clause* cl)
    { return selector.selected(cl); }

    Option<AbstractingUnifier> unify(TermList lhs, TermList rhs) const
    { return AbstractingUnifier::unify(lhs, 0, rhs, 0, uwaMode(), uwaFixedPointIteration); }
  };

#if VDEBUG
  std::shared_ptr<AlascaState> testAlascaState(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
    std::shared_ptr<InequalityNormalizer> strongNormalization = Lib::make_shared(InequalityNormalizer()),
    Ordering* ordering = nullptr,
    bool uwaFixdPointIteration = false,
    LiteralSelectors::SelectorMode mode = LiteralSelectors::selectorMode<MaximalLiteralSelector>()
    // AlascaSelector sel = AlascaSelector::fromType<MaximalLiteralSelector>(nullptr)
    );
#endif


} // namespace Kernel
 
#endif // __ALASCA_State__


