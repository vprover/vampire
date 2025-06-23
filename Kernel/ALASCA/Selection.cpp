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
#include "Kernel/ALASCA/Normalization.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/ALASCA/SelectionPrimitves.hpp"
#include "Kernel/ALASCA/Signature.hpp"
#include "Kernel/ALASCA/Term.hpp"
#include "Kernel/BestLiteralSelector.hpp"
#include "Kernel/LiteralComparators.hpp"
#include "Kernel/LiteralSelector.hpp"
#include "Kernel/MaximalLiteralSelector.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/OrderingUtils.hpp"
#include "Lib/Comparison.hpp"
#include <algorithm>

namespace Kernel {

#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }

template<class QComparator>
struct AlascaAtomComparator;

template<class C1, class C2>
struct AlascaAtomComparator<LiteralComparators::Composite<C1, C2>> {
  AlascaSelector const& self;

  template<class T>
  bool operator()(T const& l, T const& r) const {
    return AlascaAtomComparator<C1>{.self = self}(l, r) ? /* less */ true
         : AlascaAtomComparator<C1>{.self = self}(r, l) ? /* greater */ false
         : AlascaAtomComparator<C2>{.self = self}(l, r);
  } 

  template<class T>
  auto dbg(T const& t) {
    return std::make_tuple(AlascaAtomComparator<C1>{.self = self}.dbg(t), AlascaAtomComparator<C2>{.self = self}.dbg(t));
  }

};

template<class C>
struct AlascaAtomComparator<LiteralComparators::Inverse<C>> {
  AlascaSelector const& self;

  template<class T>
  bool operator()(T const& l, T const& r) const 
  { return AlascaAtomComparator<C>{.self = self}(r, l); } 

  template<class T>
  auto dbg(T const& t) {
    return Output::catOwned("inverse(", AlascaAtomComparator<C>{.self = self}.dbg(t), ")");
  }


};

template<class By>
struct AlascaAtomComparatorByKey {
  template<class T>
  bool operator()(T const& l, T const& r) const  
  { return By::getKey(l) < By::getKey(r); }

  template<class T>
  auto dbg(T const& t) {
    return By::getKey(t);
  }


};


struct NotTransparent 
{
  template<class T>
  static auto getKey(T const& x)  { return x.literal()->color() != COLOR_TRANSPARENT; }
};

template<>
struct AlascaAtomComparator<LiteralComparators::ColoredFirst> 
  : public AlascaAtomComparatorByKey<NotTransparent> 
{ AlascaSelector const& self; };


struct NoPositiveEquality {
  template<class T>
  static auto getKey(T const& x)  { return !(x.literal()->isEquality() && x.literal()->isPositive()); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::NoPositiveEquality> 
  : public AlascaAtomComparatorByKey<NoPositiveEquality>
{ AlascaSelector const& self; };

struct IsNegative {
  template<class T>
  static auto getKey(T const& x) { 
      // TODO this should be isNegativeForSelection
      return x.literal()->isNegative(); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::Negative> 
  : public AlascaAtomComparatorByKey<IsNegative> 
{ AlascaSelector const& self; };

struct IsNegativeEquality {
  template<class T>
  static auto getKey(T const& x) { return x.literal()->isEquality() && x.literal()->isNegative(); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::NegativeEquality> 
  : public AlascaAtomComparatorByKey<IsNegativeEquality> 
{ AlascaSelector const& self; };


struct Weight {
  static unsigned weight(Term* t) { return t->weight(); }
  static unsigned weight(TermList t) { return t.weight(); }

  static auto getKey(SelectedAtom const& x) { return x.selectedAtom().apply([](auto x) { return weight(x); }); }
  static auto getKey(__SelectedLiteral const& x) { return weight(x.literal()); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::MaximalSize> 
  : public AlascaAtomComparatorByKey<Weight> 
{ AlascaSelector const& self; };

struct MinusVariables {
  static int numVarOccs(Term* t) { return t->numVarOccs(); }
  static int numVarOccs(TermList t) { return t.isVar() ? 1 : numVarOccs(t.term()); }

  static auto getKey(SelectedAtom const& x) { return -int(x.selectedAtom().apply([](auto x) { return numVarOccs(x); })); }
  static auto getKey(__SelectedLiteral const& x) { return numVarOccs(x.literal()); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastVariables> 
  : public AlascaAtomComparatorByKey<MinusVariables> 
{ AlascaSelector const& self; };

struct MinusDistinctVariables {

  static int getDistinctVars(Term* t) { return t->getDistinctVars(); }
  static int getDistinctVars(TermList t) { return t.isVar() ? 1 : getDistinctVars(t.term()); }

  static auto getKey(SelectedAtom const& x) { return -int(x.selectedAtom().apply([](auto x) { return getDistinctVars(x); })); }
  static auto getKey(__SelectedLiteral const& x) { return -int(getDistinctVars(x.literal())); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastDistinctVariables> 
  : public AlascaAtomComparatorByKey<MinusDistinctVariables> 
{ AlascaSelector const& self; };

struct MinusTopLevelVariables {

  /* top level variables here does not mean alasca top level variables (e.g. x in `k x + t`), 
   * but mean variables that are arguments to the outer most function/predicate (e.g. x in `p(x, f(y))`) */

  static int varArgCount(Term* t) { return anyArgIter(t).filter([](auto t) { return t.isVar(); }).count(); }
  static int varArgCount(TermList t) { return std::numeric_limits<int>::max() - 1; }

  static auto getKey(SelectedAtom const& x) { return -int(x.selectedAtom().apply([](auto x) { return varArgCount(x); })); }
  static auto getKey(__SelectedLiteral const& x) { return -int(varArgCount(x.literal())); }
};

template<>
struct AlascaAtomComparator<LiteralComparators::LeastTopLevelVariables> 
  : public AlascaAtomComparatorByKey<MinusTopLevelVariables> 
{ AlascaSelector const& self; };

template<>
struct AlascaAtomComparator<LiteralComparators::LexComparator> {
  AlascaSelector const& self;

  template<class T>
  bool operator()(T const& l, T const& r) const 
  { 
    // TODO this is not implemented as the LexComparator, as i don't think the lex comparator has any good semantic point to it, but is only there fore tie-breaking. this can be done way more cheaply
    return l < r;
  }

  template<class T>
  auto dbg(T const& x) 
  { return "lex"; }

};

struct GetKey {

};

template<class Uninter, class FallBack, class... Inter>
struct AlascaAtomComparator<LiteralComparators::ALASCA::IfUninterpreted<Uninter,std::tuple<Inter...>, FallBack>> { 
  AlascaSelector const& self;

  bool operator()(__SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { 
    auto norml = InequalityNormalizer::normalize(l.literal()).asItp();
    auto normr = InequalityNormalizer::normalize(r.literal()).asItp();

    if (norml.isSome() == normr.isSome()) {
      return norml.isSome() 
        ? compareItp(*norml, *normr, Inter{}...) 
        : AlascaAtomComparator<Uninter>{.self = self}(l, r);
    } else {
      auto res = normr.isSome();
      switch (env.options->alascaSelection()) {
        case Shell::Options::AlascaSelectionMode::OFF:
          ASSERTION_VIOLATION
        case Shell::Options::AlascaSelectionMode::ON:
          return res;
        case Shell::Options::AlascaSelectionMode::INV:
          return !res;
      }
    }
  }

  template<class NumTraits>
  bool getKey(LiteralComparators::ALASCA::IsUwaConstraint const&, AlascaLiteralItp<NumTraits> const& lit) const {
    // TODO
    return false;
  }

  template<class NumTraits>
  unsigned getKey(LiteralComparators::ALASCA::CntSummandsMax const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return self.maxAtomsNotLessStack(lit.term()).size(); }

  template<class NumTraits>
  unsigned getKey(LiteralComparators::ALASCA::CntSummandsAll const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return lit.term().nSummands(); }

  unsigned theoryComplexity(AnyAlascaTerm t) const {
    unsigned total = 0;
    for (auto t : t.bottomUpIter()) {
      if (auto sum = t.asSum()) {
        sum->apply([&](auto& sum) {
            ASS(sum.nSummands() > 0)
            total += sum.nSummands() - 1;
            for (auto monom : sum.iterSummands()) {
              if (monom.numeral() != 1) {
                total += 1;
              }
            }
        });
      }
    }
    return total;
  }

  unsigned theoryComplexity(TypedTermList t) const {
    return theoryComplexity(InequalityNormalizer::normalize(t));
  }

  struct MultiSetUnsigned {
    Stack<unsigned> _self;
    MultiSetUnsigned(MultiSetUnsigned&&) = default;
    MultiSetUnsigned(Stack<unsigned> self) : _self(std::move(self)) 
    { _self.sort(); }
  };


  static Comparison compare(MultiSetUnsigned const& l_, MultiSetUnsigned const& r_)
  { 
    auto& l = l_._self;
    auto& r = r_._self;
    for (auto i : range(0, std::min(l.size(), r.size()))) {
      if (l[i] != r[i]) {
        return l[i] < r[i] ? Comparison::LESS : Comparison::GREATER;
      }
    }
    return Int::compare(l.size(), r.size());
  }

  template<class NumTraits>
  MultiSetUnsigned getKey(LiteralComparators::ALASCA::TheoryComplexityAll const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(lit.term().iterSummands()
      .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(LiteralComparators::ALASCA::TheoryComplexityMax const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(self.maxAtomsNotLess(lit.term())
      .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(LiteralComparators::ALASCA::SizeAll const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(lit.term().iterSummands()
      .map([&](auto x) { return x.atom().weight(); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(LiteralComparators::ALASCA::SizeMax const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(self.maxAtomsNotLess(lit.term())
      .map([&](auto x) { return x.atom().weight(); })
      .collectStack()); }


  template<class NumTraits>
  MultiSetUnsigned getKey(LiteralComparators::ALASCA::NumberOfVarsAll const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(lit.term().iterSummands()
      .map([&](auto x) { return x.atom().getDistinctVars(); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(LiteralComparators::ALASCA::NumberOfVarsMax const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(self.maxAtomsNotLess(lit.term())
      .map([&](auto x) { return x.atom().getDistinctVars(); })
      .collectStack()); }


  template<class Cmp>
  auto getKey(Cmp const& cmp, AlascaLiteralItpAny const& lit) const
  { return lit.apply([&](auto& lit) { return getKey(cmp, lit); }); }

  bool compareItp(AlascaLiteralItpAny const& l, AlascaLiteralItpAny const& r) const {
    return AlascaAtomComparator<FallBack>{.self = self}(l, r);
  }

  static Comparison compare(bool const& l, bool const& r) 
  { return Int::compare(l,r); }

  static Comparison compare(unsigned const& l, unsigned const& r) 
  { return Int::compare(l,r); }

  template<class T>
  static Comparison compare(T const& l, T const& r);

  template<class T, class... Ts>
  bool compareItp(AlascaLiteralItpAny const& l, AlascaLiteralItpAny const& r, T t, Ts... ts) const {
    auto kl = getKey(t, l);
    auto kr = getKey(t, r);
    // TODO inversion
    switch (compare(kl, kr)) {
    case Comparison::EQUAL:
      return compareItp(l, r, std::move(ts)...);
    case Comparison::GREATER: return false;
    case Comparison::LESS:    return true;
    }
    ASSERTION_VIOLATION
  }
};
 

struct AlascaSelectorDispatch {
  AlascaSelector const& self;

  template<unsigned i>
  Stack<__SelectedLiteral> computeSelected(TL::Token<GenericELiteralSelector<i>>, Clause* cl) 
  { throw UserErrorException("E literal selector not supported for alasca (yet)"); }

  template<unsigned i>
  Stack<__SelectedLiteral> computeSelected(TL::Token<GenericSpassLiteralSelector<i>>, Clause* cl) 
  { throw UserErrorException("Spass literal selector not supported for alasca (yet)"); }

  // auto iterUnproductive(Stack<SelectedAtom> const& atoms) const
  // { return arrayIter(atoms)
  //      .filter([](auto x) { return !*x.isProductive(); }); }

  // auto iterMaxLits(Ordering* ord, Stack<SelectedAtom> const& atoms) const {
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





  // auto iterMax2(Ordering* ord, Stack<SelectedAtom> const& atoms) const {
  //    return OrderingUtils::maxElems(atoms.size(),
  //                   [=](unsigned l, unsigned r)
  //                   { return AlascaOrderingUtils::compareAtom(ord, atoms[l], atoms[r]); },
  //                   [&](unsigned i)
  //                   { return atoms[i]; },
  //                   SelectionCriterion::NOT_LESS)
  //           .map([&](auto i) -> decltype(auto) { return atoms[i]; })
  //           ;
  //           // .filter([](auto& a) { return a.match(
  //           //       [](auto a) { return !a.isNumSort() || !a.selectedAtomicTerm().isVar(); },
  //           //       [](auto t) { return true; }); });
  // }


  auto iterMaxLits(Clause* const& atoms) const 
  { 
     return OrderingUtils::maxElems(atoms->size(),
                    [=](unsigned l, unsigned r)
                    { return AlascaOrderingUtils::compareAtom(self.ord, (*atoms)[l], (*atoms)[r]); },
                    [&](unsigned i)
                    { return (*atoms)[i]; },
                    SelectionCriterion::NOT_LESS)
            .map([&](auto i) -> decltype(auto) { return __SelectedLiteral(atoms, i, /* bgSelected */ false); });
  }

  template<class NumTraits>
  static bool hasUnshieldedVar(TermList term) {
    auto sig = asig(NumTraits{});
    if (term.isVar()) {
      return true;
    }
    RStack<TermList> todo;
    todo->push(term);
    while (auto term = todo->tryPop()) {
      if (term->isVar()) {
        return true;
      } else if (sig.isFloor(*term)) {
        todo->push(term->term()->termArg(0));
      } else if (sig.isLinMul(*term)) {
        todo->push(term->term()->termArg(0));
      } else if (sig.isAdd(*term)) {
        todo->push(term->term()->termArg(0));
        todo->push(term->term()->termArg(1));
      }
    }
    return false;
  }

  // template<class NumTraits>
  // static bool selectable(SelectedAtomicTermItp<NumTraits> const& s) {
  //   // we cannot select unshielded vars
  //   if (hasUnshieldedVar<NumTraits>(s.selectedSummand().atom())) 
  //     return false;
  //   return s.literal()->isEquality() ? s.literal()->isNegative() 
  //                                    : s.selectedSummand().numeral() < 0;
  // }
  //
  // static bool selectable(SelectedAtomicTermUF const& s) { return s.literal()->isNegative(); }
  // static bool selectable(SelectedAtomicTerm const& t) { return t.apply([&](auto& x) { return selectable(x); }); }
  // static bool selectable(SelectedAtomicLiteral const& l) { return l.literal()->isNegative(); }

  bool selectable(AlascaLiteralUF const& l) const { return l.toLiteral()->isNegative(); }

  template<class NumTraits>
  bool selectable(AlascaLiteralItp<NumTraits> const& l) const {
    return self.maxAtomsNotLess(l.term())
      .all([&](AlascaMonom<NumTraits> a) { 
          if (hasUnshieldedVar<NumTraits>(a.atom())) {
            return false;
          }
          switch (l.symbol()) {
            case AlascaPredicate::EQ: return false;
            case AlascaPredicate::NEQ: return true;
            case AlascaPredicate::GREATER:
            case AlascaPredicate::GREATER_EQ: return a.numeral() < 0;
          } 
          ASSERTION_VIOLATION 
       });
  }

  bool selectable(AlascaLiteral const& l) const { return l.apply([this](auto& x) { return selectable(x); }); }

  auto iterSelectable(Clause* cl) const
  { 
    return __SelectedLiteral::iter(cl, /*bgSelected=*/ true)
      .filter([this](auto l) {
          return selectable(InequalityNormalizer::normalize(l.literal()));
          // auto atoms = SelectedAtom::iter(ord, l, SelectionCriterion::NOT_LESS)
          //    .collectRStack();
          // auto selectable = iterMax2(ord,*atoms)
          //   .all([&](auto a) { return a.apply([&](auto& x) { return this->selectable(x); }); });
          // return selectable;
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

  auto selectMax(Clause* const& atoms) const 
  { return bgSelected(false, iterMaxLits(atoms)); }

  template<class Iter>
  auto selectBG(Iter iter) const 
  { return bgSelected(true, iter); }

  auto selectBG(__SelectedLiteral atom) const 
  { return selectBG(iterItems(atom)); }

  auto selectBG(SelectedAtom atom) const 
  { return selectBG(iterItems(atom)); }

  // TODO create another complete best selector that selects first the best unproductive ones and then the best productive ones

  template<class QComparator>
  Stack<__SelectedLiteral> computeSelected(TL::Token<CompleteBestLiteralSelector<QComparator>>, Clause* cl) 
  {
    auto negative = iterSelectable(cl).collectRStack();
    negative->sort([&](auto const& l, auto const& r) 
        { return AlascaAtomComparator<QComparator>{.self = self}(r,l); });
    if (negative->size() != 0) {
      return selectBG(negative[0]);
    } else {
      return selectMax(cl);
    }
  }

  template<class QComparator>
  Stack<__SelectedLiteral> computeSelected(TL::Token<BestLiteralSelector<QComparator>>, Clause* cl) 
  { return selectBG(iterAll(cl, /*bgSelected*/ true).maxBy(AlascaAtomComparator<QComparator>{.self = self}).unwrap()); }

  template<bool complete>
  Stack<__SelectedLiteral> computeSelected(TL::Token<GenericLookaheadLiteralSelector<complete>>, Clause* cl) 
  {
    ASS_REP(self._inf, "inference engine must be set when using lookahead selection")

    RStack<__SelectedLiteral> leastResults;
    auto selectable = complete 
      ? iterSelectable(cl).collectRStack()
      : iterAll(cl, /*bgSelected*/ true).collectRStack();

    auto gens = arrayIter(*selectable)
      .map([&](auto& a) { return self._inf->lookaheadResultEstimation(a); })
      .collectRStack();

    if (gens->isEmpty()) {
      ASS(complete)
      return selectMax(cl);
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
      .maxBy(AlascaAtomComparator<LiteralComparators::LookaheadComparator>{.self = self})
      .unwrap();

    return selectBG(best);
  } 


  template<bool complete>
  Stack<__SelectedLiteral> computeSelected(TL::Token<GenericRndLiteralSelector<complete>>, Clause* atoms) {
    if (complete) {
      RStack<__SelectedLiteral> negative;
      negative->loadFromIterator(iterSelectable(atoms));
      if (negative.size() != 0
          // && Random::getBit() // <- sometimes select all maximals even if there is negatives TODO do we want this really?
          ) {
        return selectBG(Random::getElem(*negative));
      } else {
        return selectMax(atoms);
      }
    } else {
      return selectBG(__SelectedLiteral(atoms, Random::getInteger(atoms->size()), /*bgSelected=*/true));
    }
  }


  Stack<__SelectedLiteral> computeSelected(TL::Token<MaximalLiteralSelector>, Clause* atoms) 
  { return selectMax(atoms); }

  Stack<__SelectedLiteral> computeSelected(TL::Token<TotalLiteralSelector>, Clause* cl) {
    return iterAll(cl, /* bgSelected */ true) .collectStack();
  }
};


Stack<__SelectedLiteral> AlascaSelector::computeSelected(Clause* cl) const
{
  DEBUG(0, "     all atoms: ", *cl)
  ASS(cl->size() > 0)
  auto out = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, cl); });
#if VAMPIRE_CLAUSE_TRACING
  auto fwd = env.options->traceForward();
  if (fwd > 0 && unsigned(fwd) == cl->number()) {
    for (auto& sel : out) {
      std::cout << "forward trace " << fwd << ": selected: " << sel << std::endl;
    }
    if (out.size() == 0) {
      std::cout << "forward trace " << fwd << ": selected: nothing" << std::endl;
    }
  }
#endif
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
