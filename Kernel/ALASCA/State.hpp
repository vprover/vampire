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

    // auto _maxLits(Clause* cl, SelectionCriterion sel) {
    //   return OrderingUtils::maxElems(
    //       cl->size(), 
    //       [=](unsigned l, unsigned r) 
    //       { return ordering->compare((*cl)[l], (*cl)[r]); },
    //       [=](unsigned i) -> Literal&
    //       { return *(*cl)[i]; },
    //       sel)
    //     .map([=](auto i) 
    //         { return SelectedLiteral(cl, i, *this); });
    // }

    template<class LitOrTerm0, class LitOrTerm1>
    bool greater(LitOrTerm0 lhs, LitOrTerm1 rhs)
    { return ordering->compare(lhs, rhs) == Ordering::Result::GREATER; }

    template<class LitOrTerm0, class LitOrTerm1>
    bool notLess(LitOrTerm0 lhs, LitOrTerm1 rhs)
    { return OrderingUtils::notLess(ordering->compare(lhs, rhs)); }

    template<class LitOrTerm0, class LitOrTerm1>
    bool notLeq(LitOrTerm0 lhs, LitOrTerm1 rhs)
    { return OrderingUtils::notLeq(ordering->compare(lhs, rhs)); }

    // TODO 1 
    // template<class NumTraits>
    // auto maxSummandIndices(AlascaLiteralItp<NumTraits> const& lit, SelectionCriterion selection)
    // { return maxSummandIndices(lit.term(), selection); }
    //

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
    //
    //
    // template<class T>
    // auto maxSummandIndices(std::shared_ptr<T> const& sum, SelectionCriterion selection)
    // { return maxSummandIndices(*sum, selection); }
    //
    // template<class T>
    // auto maxSummandIndices(Recycled<T> const& sum, SelectionCriterion selection)
    // { return maxSummandIndices(*sum, selection); }
    //
    // template<class Numeral>
    // auto maxSummandIndices(Stack<std::pair<TermList, Numeral>> const& sum, SelectionCriterion selection)
    // {
    //     auto monomAt = [=](auto i) 
    //          { return sum[i].first; }; 
    //
    //     return iterTraits(OrderingUtils::maxElems(
    //               sum.size(),
    //               [=](unsigned l, unsigned r) 
    //               { return ordering->compare(monomAt(l), monomAt(r)); },
    //               [=](unsigned i)
    //               { return monomAt(i); },
    //               selection));
    // }



    // auto maxEqIndices(Literal* lit, SelectionCriterion sel)
    // {
    //   Stack<unsigned> is(2);
    //   auto iter = [](std::initializer_list<unsigned> out)  
    //               { return arrayIter(Stack<unsigned>(out)); };
    //   switch (sel) {
    //     case SelectionCriterion::STRICTLY_MAX:
    //       switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
    //         case Ordering::Result::GREATER: return iter({0});
    //         case Ordering::Result::LESS:    return iter({1});
    //
    //         case Ordering::Result::EQUAL:
    //         case Ordering::Result::INCOMPARABLE: return iter({});
    //       }
    //
    //     case SelectionCriterion::ANY:
    //       return iter({0,1});
    //
    //     case SelectionCriterion::NOT_LESS:
    //       switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
    //         case Ordering::Result::GREATER: return iter({0});
    //         case Ordering::Result::LESS:    return iter({1});
    //
    //         case Ordering::Result::EQUAL:
    //         case Ordering::Result::INCOMPARABLE: return iter({0, 1});
    //       }
    //
    //     case SelectionCriterion::NOT_LEQ:
    //       switch (ordering->compare(lit->termArg(0), lit->termArg(1))) {
    //         case Ordering::Result::GREATER: return iter({0});
    //         case Ordering::Result::LESS:    return iter({1});
    //         case Ordering::Result::EQUAL:        return iter({});
    //         case Ordering::Result::INCOMPARABLE: return iter({0, 1});
    //       }
    //   }
    //
    //   return arrayIter(std::move(is));
    // }

    // auto selectUninterpretedEquality(SelectedLiteral lit, SelectionCriterion sel)
    // { return maxEqIndices(lit.literal(), sel)
    //     .map([lit](auto i) { return SelectedUninterpretedEquality(lit, i); }); }

    // TODO use ifElseIter
    // TODO 1 remove (?)
    // IterTraits<VirtualIterator<TypedTermList>> activePositions(Literal* l);
    // {
    //   return iterTraits(norm().tryNormalizeInterpreted(l)
    //     .match(
    //       [=](AlascaLiteralItpAny l) -> VirtualIterator<TypedTermList> {
    //         return pvi(coproductIter(std::move(l).applyCo([=](auto l)  {
    //             return maxSummandIndices(l, SelectionCriterion::NOT_LEQ)
    //                      .map([l](auto i) {
    //                          return TypedTermList(l.term().summandAt(i).atom(), l.numTraits().sort());
    //                      });
    //         })));
    //       },
    //       [=]() {
    //         if (l->isEquality()) {
    //           auto sort = l->eqArgSort();
    //           return pvi(maxEqIndices(l, SelectionCriterion::NOT_LEQ)
    //             .map([=](auto i) { return TypedTermList(l->termArg(i), sort); }));
    //         } else {
    //             return pvi(termArgIterTyped(l));
    //         }
    //       }));
    // }


    bool subtermEqModT(TypedTermList sub, TypedTermList sup)
    {
      ASS(isAtomic(sub))
      return norm().normalize(sup).toTerm()
        .containsSubterm(norm().normalize(sub).toTerm());
    }


    // auto maxSummands(SelectedLiteral sel_lit , SelectionCriterion sel) 
    // { return coproductIter(sel_lit.interpreted.unwrap()
    //             .applyCo([&](auto& lit) 
    //                    { return maxSummandIndices(lit, sel); }))
    //             .map([=](auto i) 
    //                  { return SelectedSummand(sel_lit, i); }); }


                // TODO 1 replace this by 'selected(...)'
// IterTraits<VirtualIterator<Coproduct<SelectedSummand, SelectedUninterpretedEquality, SelectedUninterpretedPredicate>>>
//     selectedActivePositions(
//         Clause* cl, SelectionCriterion selLit, 
//         SelectionCriterion selSum,
//         bool includeUnshieldedNumberVariables);
    // {
    //   using Out = Coproduct<SelectedSummand, SelectedUninterpretedEquality, SelectedUninterpretedPredicate>;
    //   return _maxLits(cl, selLit)
    //     .flatMap([=](auto sel_lit) -> VirtualIterator<Out> {
    //         auto lit = sel_lit.literal();
    //         if (sel_lit.interpreted.isSome()) {
    //           return pvi(maxSummands(sel_lit, selSum)
    //               .filter([=](auto x) { return includeUnshieldedNumberVariables || x.numTraits().apply([](auto x) { return !x.isFractional(); }) || !x.selectedAtom().isVar(); })
    //               .map([](auto x) { return Out(std::move(x)); }));
    //
    //         } else if (lit->isEquality()) {
    //           return pvi(maxEqIndices(lit, selSum)
    //                     .map([=](auto j) 
    //                         { return Out(SelectedUninterpretedEquality(sel_lit, j)); }));
    //         } else {
    //           return pvi(getSingletonIterator(Out(SelectedUninterpretedPredicate(sel_lit))));
    //         }
    //     });
    // }

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


    // auto maxAtoms(Clause* cl, SelectionCriterion criterion, bool includeUnshieldedNumberVariables) {
    //   using Out = OldSelectedAtom;
    //   auto atoms = Lib::make_shared(Stack<Out>());
    //   for (unsigned i : range(0, cl->size())) {
    //     auto l = SelectedLiteral(cl, i, *this);
    //     if (interpretedPred(l.literal())) {
    //       if (l.interpreted.isSome()) {
    //         for (auto a : maxSummands(l, criterion)) {
    //           atoms->push(Out(a));
    //         }
    //       } else {
    //         // must be an equality of uninterpreted terms
    //         ASS_REP(isUninterpretedEquality(l.literal()), *l.literal());
    //         for (auto a : selectUninterpretedEquality(l, criterion)) {
    //           atoms->push(Out(a));
    //         }
    //       }
    //     } else {
    //       atoms = Lib::make_shared(Stack<Out>());
    //       break;
    //     }
    //   }
    //
    //   return OrderingUtils::maxElems(
    //       atoms->size(), 
    //       [=](unsigned l, unsigned r) 
    //       { return ordering->compare((*atoms)[l].atom(), (*atoms)[r].atom()); },
    //       [=](unsigned i)
    //       { return (*atoms)[i].atom(); },
    //       criterion)
    //     .map([=](auto i) 
    //         { return (*atoms)[i]; })
    //   .filter([=](auto x) 
    //       { return !x.template is<SelectedSummand>() 
    //             || !x.template unwrap<SelectedSummand>().selectedAtom().isVar(); });
    // }
    //
    
    // TODO make sure we deal right with unshielded vars

    // TODO rename SelectedAtom
   auto selected(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) 
   { return selector.selected(cl, ordering); }

   // template<class NumTraits>
   // auto maxSummandIndices(AlascaTermItp<NumTraits> t, SelectionCriterion s) {
   //   return OrderingUtils::maxElems(t.nSummands(), 
   //       [](auto l, auto r) {},
   //       [](auto i) {},
   //       s);
   // }

   auto selectedSummands(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) -> DummyIter<SelectedAtomicTermItpAny>
     ;
   // { return selected(cl, selLit, selTerm, includeUnshieldedNumberVariables)
   //   .filterMap([](auto l) { return l.toSelectedAtomicTermItp(); }); }

    // auto selectedAtomicLiterals(Clause* cl, SelectionCriterion selLit) 
    //   // TODO 1.2
    // { return selected(cl, selLit, SelectionCriterion::ANY, /* includeUnshieldedNumberVariables */ false)
    // .filterMap([](auto x) { return std::move(x).template as<SelectedAtomicLiteral>(); }); }
    //
    // auto selectedAtomicTerms(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables)
    // { return selected(cl, selLit, selTerm, includeUnshieldedNumberVariables)
    //   .filterMap([](SelectedAtom x) -> Option<SelectedAtomicTerm> { 
    //       return std::move(x).template as<SelectedAtomicTerm>();
    //   }); }

    auto selectedEqualities(Clause* cl, SelectionCriterion selLit, SelectionCriterion selTerm, bool includeUnshieldedNumberVariables) -> DummyIter<SelectedEquality>
      ;
    // { return selectedAtomicTerms(cl, selLit, selTerm, includeUnshieldedNumberVariables)
        // .filterMap([](auto x) { return SelectedEquality::from(std::move(x)); }); }


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
    bool uwaFixdPointIteration = false,
    AlascaSelector sel = AlascaSelector::fromType<MaximalLiteralSelector>()
    );
#endif


} // namespace Kernel
 
#endif // __ALASCA_State__


