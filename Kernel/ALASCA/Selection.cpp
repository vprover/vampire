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
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MaximalLiteralSelector.hpp"
#include "Kernel/OrderingUtils.hpp"

namespace Kernel {

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

template<class F>
bool compareBy(NewSelectedAtom const& l, NewSelectedAtom const& r, F f) 
{ return f(l) < f(r); }

template<class QComparator>
struct AlascaAtomComparator;

template<class C1, class C2>
struct AlascaAtomComparator<LiteralComparators::Composite<C1, C2>> {
  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const {
    auto c1 = AlascaAtomComparator<C1>{}(l, r);
    return c1 != Comparison::EQUAL ? c1 : AlascaAtomComparator<C2>{}(l, r);
  } 
};

template<class C>
struct AlascaAtomComparator<LiteralComparators::Inverse<C>> {
  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return AlascaAtomComparator<C>{}(r, l); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::ColoredFirst> {
  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return x.literal()->color() != COLOR_TRANSPARENT; }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::NoPositiveEquality> {
  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return !(x.literal()->isEquality() && x.literal()->isPositive()); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::Negative> {
  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return !x.productive(); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::NegativeEquality> {
  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return x.literal()->isEquality() && x.literal()->isNegative(); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::MaximalSize> {

  static unsigned weight(Term* t) { return t->weight(); }
  static unsigned weight(TermList t) { return t.weight(); }

  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return x.selectedAtom().apply([](auto x) { return weight(x); }); }); } 
};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastVariables> {

  static int numVarOccs(Term* t) { return t->numVarOccs(); }
  static int numVarOccs(TermList t) { return t.isVar() ? 1 : numVarOccs(t.term()); }

  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(x.selectedAtom().apply([](auto x) { return numVarOccs(x); })); }); } 

};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastDistinctVariables> {

  static int getDistinctVars(Term* t) { return t->getDistinctVars(); }
  static int getDistinctVars(TermList t) { return t.isVar() ? 1 : getDistinctVars(t.term()); }

  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(x.selectedAtom().apply([](auto x) { return getDistinctVars(x); })); }); } 

};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastTopLevelVariables> {
  /* top level variables here does not mean alasca top level variables (e.g. x in `k x + t`), 
   * but mean variables that are arguments to the outer most function/predicate (e.g. x in `p(x, f(y))`) */

  static int varArgCount(Term* t) { return anyArgIter(t).filter([](auto t) { return t.isVar(); }).count(); }
  static int varArgCount(TermList t) { return std::numeric_limits<int>::max() - 1; }

  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { return compareBy(r, l, 
      [](auto x) { return -int(x.selectedAtom().apply([](auto x) { return varArgCount(x); })); }); }
};


template<>
struct AlascaAtomComparator<LiteralComparators::LexComparator> {

  bool operator()(NewSelectedAtom const& l, NewSelectedAtom const& r) const 
  { 
    // TODO this is not implemented as the LexComparator, as i don't think the lex comparator has any good semantic point to it, but is only there fore tie-breaking. this can be done way more cheaply
    return l < r;
  }

};


struct AlascaSelectorDispatch {
  AlascaSelector const& self;

  template<unsigned i>
  Stack<NewSelectedAtom> computeSelected(TL::Token<GenericELiteralSelector<i>>, Stack<NewSelectedAtom> atoms, Ordering* ord) 
  { throw new UserErrorException("E literal selector not supported for alasca (yet)"); }

  template<unsigned i>
  Stack<NewSelectedAtom> computeSelected(TL::Token<GenericSpassLiteralSelector<i>>, Stack<NewSelectedAtom> atoms, Ordering* ord) 
  { throw new UserErrorException("Spass literal selector not supported for alasca (yet)"); }

  auto iterUnproductive(Stack<NewSelectedAtom> const& atoms) const
  { return arrayIter(atoms)
       .filter([](auto x) { return !x.productive(); }); }

  auto iterMax(Ordering* ord, Stack<NewSelectedAtom> const& atoms) const {
     return OrderingUtils::maxElems(atoms.size(),
                    [=](unsigned l, unsigned r)
                    { return AlascaOrderingUtils::compareAtom(ord, atoms[l], atoms[r]); },
                    [&](unsigned i)
                    { return atoms[i]; },
                    SelectionCriterion::NOT_LESS)
            .map([&](auto i) -> decltype(auto) { return atoms[i]; })
            .filter([](auto& a) { return a.match(
                  [](auto a) { return !a.isNumSort() || !a.selectedAtomicTerm().isVar(); },
                  [](auto t) { return true; }); });
  }

  // TODO create another complete best selector that selects first the best unproductive ones and then the best productive ones

  template<class QComparator>
  Stack<NewSelectedAtom> computeSelected(TL::Token<CompleteBestLiteralSelector<QComparator>>, Stack<NewSelectedAtom> atoms, Ordering* ord) 
  {
    auto negative = iterUnproductive(atoms).cloned().collectRStack();
    negative->sort([&](auto& l, auto& r) { return AlascaAtomComparator<QComparator>{}(r, l); });
    if (negative->size() != 0) {
      return { negative[0] };
    } else {
      return iterMax(ord, atoms).cloned().collectStack();
    }
  }

  template<class QComparator>
  Stack<NewSelectedAtom> computeSelected(TL::Token<BestLiteralSelector<QComparator>>, Stack<NewSelectedAtom> atoms, Ordering* ord) 
  {
    return { arrayIter(atoms).maxBy(AlascaAtomComparator<QComparator>{}).unwrap() };
  }

  template<class T>
  Stack<NewSelectedAtom> computeSelected(TL::Token<T>, Stack<NewSelectedAtom> atoms, Ordering* ord) {
    ASSERTION_VIOLATION_REP("TODO")
  }

  Stack<NewSelectedAtom> computeSelected(TL::Token<TotalLiteralSelector>, Stack<NewSelectedAtom> atoms, Ordering* ord)
  { return atoms; }

  Stack<NewSelectedAtom> computeSelected(TL::Token<MaximalLiteralSelector>, Stack<NewSelectedAtom> atoms, Ordering* ord)
  { return iterMax(ord, atoms).cloned().collectStack(); }


  template<bool complete>
  Stack<NewSelectedAtom> computeSelected(TL::Token<GenericRndLiteralSelector<complete>>, Stack<NewSelectedAtom> atoms, Ordering* ord) {
    if (complete) {
      RStack<NewSelectedAtom> negative;
      negative->loadFromIterator(iterUnproductive(atoms));
      if (negative.size() != 0
          // && Random::getBit() // <- sometimes select all maximals even if there is negatives TODO do we want this really?
          ) {
        return { Random::getElem(*negative) };
      } else {
        return iterMax(ord, atoms).cloned().collectStack();
      }
    } else {
      return { Random::getElem(atoms) };
    }
  }

};


Stack<NewSelectedAtom> AlascaSelector::computeSelected(Stack<NewSelectedAtom> atoms, Ordering* ord) const
{
  DEBUG(0, "     all atoms: ", atoms)
  ASS(atoms.size() > 0)
  auto out = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, std::move(atoms), ord); });
  DEBUG(0, "selected atoms: ", out)
  return out;
}

} // namespace Kernel
