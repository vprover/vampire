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
 * Defines functions and structures that are shared by all ALASCA inference rules in order to select literals, terms, etc.
 */

#ifndef __ALASCA_State__
#define __ALASCA_State__

#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"

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
          bool fixedPointIteration
        )
      : _normalizer(std::move(normalizer))
      , ordering(std::move(ordering))
      , uwa(uwa) 
      , uwaFixedPointIteration(fixedPointIteration)
    {}

  public:
    std::shared_ptr<InequalityNormalizer> _normalizer;
    Ordering* const ordering;
    Shell::Options::UnificationWithAbstraction uwa;
    bool const uwaFixedPointIteration;

    InequalityNormalizer& norm() const { return *_normalizer; }
    std::shared_ptr<InequalityNormalizer> normalizerPtr() const { return _normalizer; }

    Shell::Options::UnificationWithAbstraction uwaMode() const { return uwa; }


    static std::shared_ptr<AlascaState> create(
          std::shared_ptr<InequalityNormalizer> normalizer,
          Ordering* const ordering,
          Shell::Options::UnificationWithAbstraction const uwa,
          bool const fixedPointIteration
        ) 
    {
      globalState = Lib::make_shared(AlascaState(std::move(normalizer), ordering, uwa, fixedPointIteration));
      return globalState;
    }

    bool isAtomic(Term* t) const
    { return forAllNumTraits([&](auto n) { return asig(n).isAtomic(t); }); }

    bool isAtomic(TermList t) const { return t.isTerm() && isAtomic(t.term()); }

    auto maxLits(Clause* cl, SelectionCriterion sel) {
      return OrderingUtils::maxElems(
          cl->size(), 
          [=](unsigned l, unsigned r) 
          { return ordering->compare((*cl)[l], (*cl)[r]); },
          [=](unsigned i) -> Literal&
          { return *(*cl)[i]; },
          sel)
        .map([=](auto i) 
            { return SelectedLiteral(cl, i, *this); });
    }

    template<class LitOrTerm>
    bool greater(LitOrTerm lhs, LitOrTerm rhs)
    { return ordering->compare(lhs, rhs) == Ordering::Result::GREATER; }

    template<class LitOrTerm>
    bool notLess(LitOrTerm lhs, LitOrTerm rhs)
    { return OrderingUtils::notLess(ordering->compare(lhs, rhs)); }

    template<class LitOrTerm>
    bool notLeq(LitOrTerm lhs, LitOrTerm rhs)
    { return OrderingUtils::notLeq(ordering->compare(lhs, rhs)); }

    template<class NumTraits>
    auto maxSummandIndices(AlascaLiteral<NumTraits> const& lit, SelectionCriterion selection)
    {
        // TODO optimize less denormalization
        auto monomAt = [=](auto i) 
             { return lit.term().summandAt(i).factors->denormalize(); }; 

        return iterTraits(OrderingUtils::maxElems(
                  lit.term().nSummands(),
                  [=](unsigned l, unsigned r) 
                  { return ordering->compare(monomAt(l), monomAt(r)); },
                  [=](unsigned i)
                  { return monomAt(i); },
                  selection))
                 .filter([=](auto& i) { return selection == SelectionCriterion::NOT_LEQ ? !lit.term().summandAt(i).isNumeral()
                                            : selection == SelectionCriterion::NOT_LESS ? !lit.term().summandAt(i).isNumeral() // <- TODO re-think about this case. i think we stay complete in this case but I can't say 100% for sure.
                                            : true; });
    }


    template<class T>
    auto maxSummandIndices(std::shared_ptr<T> const& sum, SelectionCriterion selection)
    { return maxSummandIndices(*sum, selection); }

    template<class T>
    auto maxSummandIndices(Recycled<T> const& sum, SelectionCriterion selection)
    { return maxSummandIndices(*sum, selection); }

    template<class Numeral>
    auto maxSummandIndices(Stack<std::pair<TermList, Numeral>> const& sum, SelectionCriterion selection)
    {
        auto monomAt = [=](auto i) 
             { return sum[i].first; }; 

        return iterTraits(OrderingUtils::maxElems(
                  sum.size(),
                  [=](unsigned l, unsigned r) 
                  { return ordering->compare(monomAt(l), monomAt(r)); },
                  [=](unsigned i)
                  { return monomAt(i); },
                  selection));
    }



    auto maxEqIndices(Literal* lit, SelectionCriterion sel)
    {
      Stack<unsigned> is(2);
      auto iter = [](std::initializer_list<unsigned> out)  
                  { return arrayIter(Stack<unsigned>(out)); };
      switch (sel) {
        case SelectionCriterion::STRICTLY_MAX:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});

            case Ordering::Result::EQUAL:
            case Ordering::Result::INCOMPARABLE: return iter({});
          }

        case SelectionCriterion::ANY:
          return iter({0,1});

        case SelectionCriterion::NOT_LESS:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});

            case Ordering::Result::EQUAL:
            case Ordering::Result::INCOMPARABLE: return iter({0, 1});
          }

        case SelectionCriterion::NOT_LEQ:
          switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
            case Ordering::Result::GREATER: return iter({0});
            case Ordering::Result::LESS:    return iter({1});
            case Ordering::Result::EQUAL:        return iter({});
            case Ordering::Result::INCOMPARABLE: return iter({0, 1});
          }
      }

      return arrayIter(std::move(is));
    }

    auto selectUninterpretedEquality(SelectedLiteral lit, SelectionCriterion sel)
    { return maxEqIndices(lit.literal(), sel)
        .map([lit](auto i) { return SelectedUninterpretedEquality(lit, i); }); }

    auto activePositions(Literal* l) -> IterTraits<VirtualIterator<TermList>>
    {
      return iterTraits(norm().tryNormalizeInterpreted(l)
        .match(
          [=](AnyAlascaLiteral l) -> VirtualIterator<TermList> {
            return pvi(coproductIter(std::move(l).applyCo([=](auto l)  {
                return maxSummandIndices(l, SelectionCriterion::NOT_LEQ)
                         .map([l](auto i) {
                             return l.term().summandAt(i).factors->denormalize();
                         });
            })));
          },
          [=]() {
            if (l->isEquality()) {
              return pvi(maxEqIndices(l, SelectionCriterion::NOT_LEQ)
                .map([=](auto i) { return l->termArg(i); }));
            } else {
                return pvi(termArgIter(l));
            }
          }));
    }


    bool subtermEqModT(TermList sub, TermList sup)
    {
      ASS(isAtomic(sub))
      return norm().normalize(sup).denormalize()
        .containsSubterm(norm().normalize(sub).denormalize());
    }


    auto maxSummands(SelectedLiteral sel_lit , SelectionCriterion sel) 
    { return coproductIter(sel_lit.interpreted.unwrap()
                .applyCo([&](auto& lit) 
                       { return maxSummandIndices(lit, sel); }))
                .map([=](auto i) 
                     { return SelectedSummand(sel_lit, i); }); }


    auto selectedActivePositions(
        Clause* cl, SelectionCriterion selLit, 
        SelectionCriterion selSum,
        bool includeUnshieldedNumberVariables)
    {
      using Out = Coproduct<SelectedSummand, SelectedUninterpretedEquality, SelectedUninterpretedPredicate>;
      return maxLits(cl, selLit)
        .flatMap([=](auto sel_lit) -> VirtualIterator<Out> {
            auto lit = sel_lit.literal();
            if (sel_lit.interpreted.isSome()) {
              return pvi(maxSummands(sel_lit, selSum)
                  .filter([=](auto x) { return includeUnshieldedNumberVariables || x.numTraits().apply([](auto x) { return !x.isFractional(); }) || !x.selectedAtom().isVar(); })
                  .map([](auto x) { return Out(std::move(x)); }));

            } else if (lit->isEquality()) {
              return pvi(maxEqIndices(lit, selSum)
                        .map([=](auto j) 
                            { return Out(SelectedUninterpretedEquality(sel_lit, j)); }));
            } else {
              return pvi(getSingletonIterator(Out(SelectedUninterpretedPredicate(sel_lit))));
            }
        });
    }

    auto isUninterpreted(Literal* l) const 
    { return !l->isEquality() && norm().tryNormalizeInterpreted(l).isNone(); }

    auto selectedUninterpretedLiterals(Clause* cl, SelectionCriterion selLit) {
      return maxLits(cl, selLit)
        .filter([&](auto& lit) { return isUninterpreted(lit.literal()); });
    }


    auto selectedEqualities(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) {
      using Out = SelectedEquality;
      return selectedActivePositions(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        .filterMap([](auto x) -> Option<Out>
                   { return x.match(
                       [](SelectedSummand& x) {
                          return x.isInequality() ? Option<Out>()
                              : x.numTraits().template is<IntTraits>() ? Option<Out>(Out(SelectedIntegerEquality(std::move(x))))
                              : Option<Out>(Out(std::move(x)));
                       },

                       [](SelectedUninterpretedEquality& x) 
                       { return Option<Out>(Out(std::move(x))); },

                       [](SelectedUninterpretedPredicate&) 
                       { return Option<Out>(); });
        });
    }


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


    auto maxAtoms(Clause* cl, SelectionCriterion criterion, bool includeUnshieldedNumberVariables) {
      using Out = SelectedAtom;
      auto atoms = Lib::make_shared(Stack<Out>());
      for (unsigned i : range(0, cl->size())) {
        auto l = SelectedLiteral(cl, i, *this);
        if (interpretedPred(l.literal())) {
          if (l.interpreted.isSome()) {
            for (auto a : maxSummands(l, criterion)) {
              atoms->push(Out(a));
            }
          } else {
            // must be an equality of uninterpreted terms
            ASS_REP(isUninterpretedEquality(l.literal()), *l.literal());
            for (auto a : selectUninterpretedEquality(l, criterion)) {
              atoms->push(Out(a));
            }
          }
        } else {
          atoms = Lib::make_shared(Stack<Out>());
          break;
        }
      }

      return OrderingUtils::maxElems(
          atoms->size(), 
          [=](unsigned l, unsigned r) 
          { return ordering->compare((*atoms)[l].atom(), (*atoms)[r].atom()); },
          [=](unsigned i)
          { return (*atoms)[i].atom(); },
          criterion)
        .map([=](auto i) 
            { return (*atoms)[i]; })
      .filter([=](auto x) 
          { return !x.template is<SelectedSummand>() 
                || !x.template unwrap<SelectedSummand>().selectedAtom().isVar(); });
    }


    auto selectedSummands(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) {
      using Out = SelectedSummand;
      return selectedActivePositions(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        .filterMap([](auto x) -> Option<Out> {
            return x.match(
                 [](SelectedSummand& x) 
                 { return Option<Out>(std::move(x)); },

                 [](SelectedUninterpretedEquality&) 
                 { return Option<Out>(); },

                 [](SelectedUninterpretedPredicate&) 
                 { return Option<Out>(); });
        });
    }

  public:

    Option<AbstractingUnifier> unify(TermList lhs, TermList rhs) const
    { return AbstractingUnifier::unify(lhs, 0, rhs, 0, uwaMode(), uwaFixedPointIteration); }


    template<class LitOrTerm, class Iter>
    bool strictlyMaximal(LitOrTerm pivot, Iter lits)
    {
      bool found = false;
      for (auto lit : iterTraits(lits)) {
        if (lit == pivot) {
          if (found)  {
            return false;
          } else {
            found = true;
          }
        }
        if (ordering->compare(pivot, lit) == Ordering::LESS) {
          return false;
        }
      }
      ASS(found)
      return true;
    }
  };

#if VDEBUG
  std::shared_ptr<AlascaState> testAlascaState(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ALASCA_MAIN,
    std::shared_ptr<InequalityNormalizer> strongNormalization = Lib::make_shared(InequalityNormalizer()),
    Ordering* ordering = nullptr,
    bool uwaFixdPointIteration = false
    );
#endif


} // namespace Kernel
 
#endif // __ALASCA_State__


