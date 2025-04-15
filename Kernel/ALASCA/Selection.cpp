/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#include "Selection.hpp"
#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/BestLiteralSelector.hpp"
#include "Kernel/LiteralComparators.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MaximalLiteralSelector.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

template<class T, class F>
bool compareBy(T const& l, T const& r, F f) 
{ return f(l) < f(r); }

template<class QComparator>
struct AlascaAtomComparator;

template<class C1, class C2>
struct AlascaAtomComparator<LiteralComparators::Composite<C1, C2>> {

  template<class T>
  bool operator()(T const& l, T const& r) const {
    auto c1 = AlascaAtomComparator<C1>{}(l, r);
    return c1 != Comparison::EQUAL ? c1 : AlascaAtomComparator<C2>{}(l, r);
  } 

};

template<class C>
struct AlascaAtomComparator<LiteralComparators::Inverse<C>> {
  template<class T>
  bool operator()(T const& l, T const& r) const 
  { return AlascaAtomComparator<C>{}(r, l); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::ColoredFirst> {

  template<class T>
  bool operator()(T const& l, T const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return x.literal()->color() != COLOR_TRANSPARENT; }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::NoPositiveEquality> {
  template<class T>
  bool operator()(T const& l, T const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return !(x.literal()->isEquality() && x.literal()->isPositive()); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::Negative> {
  template<class T>
  bool operator()(T const& l, T const& r) const 
  { return compareBy(r, l, 
      [](auto x) { 
      // TODO this should be isNegativeForSelection
      return x.literal()->isNegative(); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::NegativeEquality> {
  template<class T>
  bool operator()(T const& l, T const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return x.literal()->isEquality() && x.literal()->isNegative(); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::MaximalSize> {

  static unsigned weight(Term* t) { return t->weight(); }
  static unsigned weight(TermList t) { return t.weight(); }

  bool operator()(SelectedAtom const& l, SelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return x.selectedAtom().apply([](auto x) { return weight(x); }); }); } 

  bool operator()(__SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return weight(x.literal()); }); } 

};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastVariables> {

  static int numVarOccs(Term* t) { return t->numVarOccs(); }
  static int numVarOccs(TermList t) { return t.isVar() ? 1 : numVarOccs(t.term()); }

  bool operator()(SelectedAtom const& l, SelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(x.selectedAtom().apply([](auto x) { return numVarOccs(x); })); }); } 

  bool operator()(__SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return numVarOccs(x.literal()); }); } 

};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastDistinctVariables> {

  static int getDistinctVars(Term* t) { return t->getDistinctVars(); }
  static int getDistinctVars(TermList t) { return t.isVar() ? 1 : getDistinctVars(t.term()); }

  bool operator()(SelectedAtom const& l, SelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(x.selectedAtom().apply([](auto x) { return getDistinctVars(x); })); }); } 


  bool operator()(__SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(getDistinctVars(x.literal())); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastTopLevelVariables> {
  /* top level variables here does not mean alasca top level variables (e.g. x in `k x + t`), 
   * but mean variables that are arguments to the outer most function/predicate (e.g. x in `p(x, f(y))`) */

  static int varArgCount(Term* t) { return anyArgIter(t).filter([](auto t) { return t.isVar(); }).count(); }
  static int varArgCount(TermList t) { return std::numeric_limits<int>::max() - 1; }

  bool operator()(SelectedAtom const& l, SelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(x.selectedAtom().apply([](auto x) { return varArgCount(x); })); }); }

  bool operator()(__SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(varArgCount(x.literal())); }); }
};


template<>
struct AlascaAtomComparator<LiteralComparators::LexComparator> {

  template<class T>
  bool operator()(T const& l, T const& r) const 
  { 
    // TODO this is not implemented as the LexComparator, as i don't think the lex comparator has any good semantic point to it, but is only there fore tie-breaking. this can be done way more cheaply
    return l < r;
  }

};


struct AlascaSelectorDispatch {
  AlascaSelector const& self;

  template<unsigned i>
  Stack<SelectedAtom> computeSelected(TL::Token<GenericELiteralSelector<i>>, Stack<SelectedAtom> atoms, Ordering* ord) 
  { throw new UserErrorException("E literal selector not supported for alasca (yet)"); }

  template<unsigned i>
  Stack<SelectedAtom> computeSelected(TL::Token<GenericSpassLiteralSelector<i>>, Stack<SelectedAtom> atoms, Ordering* ord) 
  { throw new UserErrorException("Spass literal selector not supported for alasca (yet)"); }

  // auto iterUnproductive(Stack<SelectedAtom> const& atoms) const
  // { return arrayIter(atoms)
  //      .filter([](auto x) { return !*x.isProductive(); }); }

  // auto iterMax(Ordering* ord, Stack<SelectedAtom> const& atoms) const {
  //    return OrderingUtils::maxElems(atoms.size(),
  //                   [=](unsigned l, unsigned r)
  //                   { return AlascaOrderingUtils::compareAtom(ord, atoms[l], atoms[r]); },
  //                   [&](unsigned i)
  //                   { return atoms[i]; },
  //                   SelectionCriterion::NOT_LESS)
  //           .map([&](auto i) -> decltype(auto) { return atoms[i]; })
  //           .filter([](auto& a) { return a.match(
  //                 [](auto a) { return !a.isNumSort() || !a.selectedAtomicTerm().isVar(); },
  //                 [](auto t) { return true; }); });
  // }
  //
  auto iterMax2(Ordering* ord, Stack<SelectedAtom> const& atoms) const {
     return OrderingUtils::maxElems(atoms.size(),
                    [=](unsigned l, unsigned r)
                    { return AlascaOrderingUtils::compareAtom(ord, atoms[l], atoms[r]); },
                    [&](unsigned i)
                    { return atoms[i]; },
                    SelectionCriterion::NOT_LESS)
            .map([&](auto i) -> decltype(auto) { return atoms[i]; })
            ;
            // .filter([](auto& a) { return a.match(
            //       [](auto a) { return !a.isNumSort() || !a.selectedAtomicTerm().isVar(); },
            //       [](auto t) { return true; }); });
  }


  auto iterMax(Ordering* ord, Clause* const& atoms) const 
  { 
     return OrderingUtils::maxElems(atoms->size(),
                    [=](unsigned l, unsigned r)
                    { return AlascaOrderingUtils::compareAtom(ord, (*atoms)[l], (*atoms)[r]); },
                    [&](unsigned i)
                    { return (*atoms)[i]; },
                    SelectionCriterion::NOT_LESS)
            .map([&](auto i) -> decltype(auto) { return __SelectedLiteral(atoms, i, /* bgSelected */ false); });
  }

  template<class NumTraits>
  static bool selectable(SelectedAtomicTermItp<NumTraits> const& s) {
    // we cannot select unshielded vars
    if (s.selectedSummand().atom().isVar()) 
      return false;
    return s.literal()->isEquality() ? s.literal()->isNegative() 
                                     : s.selectedSummand().numeral() < 0;
  }

  static bool selectable(SelectedAtomicTermUF const& s) { return s.literal()->isNegative(); }
  static bool selectable(SelectedAtomicTerm const& t) { return t.apply([&](auto& x) { return selectable(x); }); }
  static bool selectable(SelectedAtomicLiteral const& l) { return l.literal()->isNegative(); }

  auto iterSelectable(Ordering* ord, Clause* cl) const
  { 
    return __SelectedLiteral::iter(cl, /*bgSelected=*/ true)
      .filter([ord, this](auto l) {
          auto atoms = SelectedAtom::iter(ord, l, SelectionCriterion::NOT_LESS)
             .collectRStack();
          auto selectable = iterMax2(ord,*atoms)
            .all([&](auto a) { return a.apply([&](auto& x) { return this->selectable(x); }); });
          return selectable;
      });
  }

  static auto iterAll(Clause* cl, bool bgSelected) {
    return range(0, cl->size())
            .map([=](auto i) { return __SelectedLiteral(cl, i, bgSelected); });
  }


  template<class Iter>
  auto bgSelected(bool bgSelected, Iter iter) const
  { return iter.map([&](auto x) { x.setBGSelected(bgSelected); return x; })
      .inspect([](auto& x) { return x.isBGSelected(); })
      .collectStack(); }

  auto selectMax(Ordering* ord, Clause* const& atoms) const 
  { return bgSelected(false, iterMax(ord, atoms)); }

  template<class Iter>
  auto selectBG(Iter iter) const 
  { return bgSelected(true, iter); }

  auto selectBG(__SelectedLiteral atom) const 
  { return selectBG(iterItems(atom)); }

  auto selectBG(SelectedAtom atom) const 
  { return selectBG(iterItems(atom)); }

  // TODO create another complete best selector that selects first the best unproductive ones and then the best productive ones

  template<class QComparator>
  Stack<__SelectedLiteral> computeSelected(TL::Token<CompleteBestLiteralSelector<QComparator>>, Clause* cl, Ordering* ord) 
  {
    auto negative = iterSelectable(ord, cl).collectRStack();
    negative->sort([&](auto& l, auto& r) { return AlascaAtomComparator<QComparator>{}(r, l); });
    if (negative->size() != 0) {
      return selectBG(negative[0]);
    } else {
      return selectMax(ord, cl);
    }
  }

  template<class QComparator>
  Stack<__SelectedLiteral> computeSelected(TL::Token<BestLiteralSelector<QComparator>>, Clause* cl, Ordering* ord) 
  { return selectBG(iterAll(cl, /*bgSelected*/ true).maxBy(AlascaAtomComparator<QComparator>{}).unwrap()); }

  template<bool complete>
  Stack<__SelectedLiteral> computeSelected(TL::Token<GenericLookaheadLiteralSelector<complete>>, Clause* cl, Ordering* ord) 
  {
    // TODO

    auto sa = Saturation::SaturationAlgorithm::tryGetInstance();

    RStack<__SelectedLiteral> leastResults;
    auto selectable = complete 
      ? iterSelectable(ord,cl).collectRStack()
      : iterAll(cl, /*bgSelected*/ true).collectRStack();
    auto gens = arrayIter(*selectable)
      // .filter([](auto r) { return complete ? !*r.isProductive() : true; })
      .map([&](auto& a) { return sa->lookaheadResultEstimation(a); })
      .collectRStack();

    if (gens->isEmpty()) {
      ASS(complete)
      return selectMax(ord, cl);
    }
    
     while (leastResults->isEmpty()) {
      for (auto i : range(0, gens->size())) {

        if (gens[i].hasNext()) {
          gens[i].next();
        } else {
          leastResults->push(selectable[i]);
        }
      }
    }

    auto best = arrayIter(*leastResults)
      .maxBy(AlascaAtomComparator<LiteralComparators::LookaheadComparator>{})
      .unwrap();

    return selectBG(best);
  } 


  template<bool complete>
  Stack<__SelectedLiteral> computeSelected(TL::Token<GenericRndLiteralSelector<complete>>, Clause* atoms, Ordering* ord) {
    if (complete) {
      RStack<__SelectedLiteral> negative;
      negative->loadFromIterator(iterSelectable(ord, atoms));
      if (negative.size() != 0
          // && Random::getBit() // <- sometimes select all maximals even if there is negatives TODO do we want this really?
          ) {
        return selectBG(Random::getElem(*negative));
      } else {
        return selectMax(ord, atoms);
      }
    } else {
      return selectBG(__SelectedLiteral(atoms, Random::getInteger(atoms->size()), /*bgSelected=*/true));
    }
  }


  Stack<__SelectedLiteral> computeSelected(TL::Token<MaximalLiteralSelector>, Clause* atoms, Ordering* ord) 
  { return selectMax(ord, atoms); }

  Stack<__SelectedLiteral> computeSelected(TL::Token<TotalLiteralSelector>, Clause* cl, Ordering* ord) {
    return iterAll(cl, /* bgSelected */ true) .collectStack();
  }

  template<class C>
  Stack<__SelectedLiteral> computeSelected(TL::Token<C>, Clause* atoms, Ordering* ord) {
    ASSERTION_VIOLATION_REP(Output::cat("TODO: ", C::typeName()))
  }



};


Stack<__SelectedLiteral> AlascaSelector::computeSelected(Clause* cl, Ordering* ord) const
{
  DEBUG(0, "     all atoms: ", *cl)
  ASS(cl->size() > 0)
  auto out = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, cl, ord); });
  DEBUG(0, "selected atoms: ", out)
  return out;
}


// Stack<SelectedAtom> AlascaSelector::computeSelected(Stack<SelectedAtom> atoms, Ordering* ord) const
// {
//   DEBUG(0, "     all atoms: ", atoms)
//   ASS(atoms.size() > 0)
//   auto out = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, std::move(atoms), ord); });
//   DEBUG(0, "selected atoms: ", out)
//   return out;
// }

} // namespace Kernel
