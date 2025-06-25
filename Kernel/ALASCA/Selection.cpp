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

template<class T>
struct TotalComparableMultiset {
  Stack<T> _self;
  TotalComparableMultiset(TotalComparableMultiset&&) = default;
  TotalComparableMultiset(Stack<T> self) : _self(std::move(self)) 
  { _self.sort(); }
};

template<class T>
TotalComparableMultiset(Stack<T>) -> TotalComparableMultiset<T>;


template<class T>
struct AlascaComparatorByLiteralKey { static constexpr bool enabled = false; };

#define BY_LITERAL_KEY(Type, body)                                                        \
  template<>                                                                              \
  struct AlascaComparatorByLiteralKey<Type>                                               \
  {                                                                                       \
    static constexpr bool enabled = true;                                                 \
    template<class Self>                                                                  \
    static auto getKey(TL::Token<Type>, Self const& self, __SelectedLiteral const& x)     \
      body                                                                                \
  };                                                                                      \

BY_LITERAL_KEY(LiteralComparators::ColoredFirst, 
  { return x.literal()->color() != COLOR_TRANSPARENT; })

BY_LITERAL_KEY(LiteralComparators::NoPositiveEquality, 
  { return !(x.literal()->isEquality() && x.literal()->isPositive()); })

// TODO this should be isNegativeForSelection (?)
BY_LITERAL_KEY(LiteralComparators::Negative, 
  { return x.literal()->isNegative(); })

BY_LITERAL_KEY(LiteralComparators::NegativeEquality, 
  { return x.literal()->isEquality() && x.literal()->isNegative(); })

BY_LITERAL_KEY(LiteralComparators::MaximalSize, 
  { return x.literal()->weight(); })

BY_LITERAL_KEY(LiteralComparators::LeastVariables, 
  { return -int(x.literal()->numVarOccs()); })

BY_LITERAL_KEY(LiteralComparators::LeastDistinctVariables, 
  { return -int(x.literal()->getDistinctVars()); })

  /* top level variables here does not mean alasca top level variables (e.g. x in `k x + t`), 
   * but mean variables that are arguments to the outer most function/predicate (e.g. x in `p(x, f(y))`) */
BY_LITERAL_KEY(LiteralComparators::LeastTopLevelVariables,
  { return -int(anyArgIter(x.literal()).filter([](auto t) { return t.isVar(); }).count()); })


#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
struct AlascaComparator {
  AlascaSelector const& self;

  AlascaComparator(AlascaSelector const& self) : self(self) {}


  template<class C1, class C2>
  Comparison compare(TL::Token<LiteralComparators::Composite<C1, C2>>, __SelectedLiteral const& l, __SelectedLiteral const& r) const {
    auto res = compare(TL::Token<C1>{}, l, r);
    return res != Comparison::EQUAL ? res : compare(TL::Token<C2>{}, l, r);
  } 

  template<class C>
  Comparison compare(TL::Token<LiteralComparators::Inverse<C>>, __SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { return compare(TL::Token<C>{}, r, l); } 

  template<class C, std::enable_if_t<AlascaComparatorByLiteralKey<C>::enabled, bool> = true>
  Comparison compare(TL::Token<C> c, __SelectedLiteral const& l, __SelectedLiteral const& r) const  
  { return Int::compare(
      AlascaComparatorByLiteralKey<C>::getKey(c, self, l), 
      AlascaComparatorByLiteralKey<C>::getKey(c, self, r)); }

  template<class T>
  Comparison compare(TL::Token<LiteralComparators::LexComparator>, T const& l, T const& r) const 
  { 
    // TODO this is not implemented as the LexComparator, as i don't think the lex comparator has any good semantic point to it, but is only there fore tie-breaking. this can be done way more cheaply
    return l == r ? Comparison::EQUAL
         : l < r ? Comparison::LESS
         : Comparison::GREATER;
  }

  template<class Uninter, class FallBack, class... Inter>
  Comparison compare(TL::Token<LiteralComparators::ALASCA::IfUninterpreted<Uninter,std::tuple<Inter...>, FallBack>> c, __SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { 
    auto norml = InequalityNormalizer::normalize(l.literal()).asItp();
    auto normr = InequalityNormalizer::normalize(r.literal()).asItp();

    if (norml.isSome() == normr.isSome()) {
      return norml.isSome() 
        ? compareItp(c, *norml, *normr, TL::Token<Inter>{}...)
        : compare(TL::Token<Uninter>{}, l, r);
    } else {
      auto res = normr.isSome() ? Comparison::LESS : Comparison::GREATER;
      switch (env.options->alascaSelection()) {
        case Shell::Options::AlascaSelectionMode::OFF:
          ASSERTION_VIOLATION
        case Shell::Options::AlascaSelectionMode::ON:
          return res;
        case Shell::Options::AlascaSelectionMode::INV:
          return revert(res);
      }
    }
  }

#define BY_INTERPRETED_KEY(Type, body)                                                    \
  template<class NumTraits>                                                               \
  auto getKey(TL::Token<LiteralComparators::ALASCA::Type>, AlascaLiteralItp<NumTraits> const& lit) const \
    body                                                                                  \
                                                                                          \
  Options::AlascaSelectionMode optionValue(TL::Token<LiteralComparators::ALASCA::Type>) const { \
    static Options::AlascaSelectionMode val = env.options->alascaSelection ## Type();     \
    return val;                                                                           \
  }                                                                                       \

  BY_INTERPRETED_KEY(IsUwaConstraint,
    {
      // TODO
      return lit.symbol() == AlascaPredicate::NEQ;
    })

  BY_INTERPRETED_KEY(CntSummandsMax,
      { return self.maxAtomsNotLessStack(lit.term()).size(); })

  BY_INTERPRETED_KEY(CntSummandsAll, 
    { return lit.term().nSummands(); })

  std::pair<unsigned, unsigned> theoryComplexity(AnyAlascaTerm t) const {
    unsigned totalNumerals = 0;
    unsigned totalPlus     = 0;
    for (auto t : t.bottomUpIter()) {
      if (auto sum = t.asSum()) {
        sum->apply([&](auto& sum) {
            if (sum.nSummands() == 0) {
              totalNumerals += 1;
            } else {
              totalPlus += sum.nSummands() - 1;
              for (auto monom : sum.iterSummands()) {
                if (monom.numeral() != 1) {
                  totalNumerals += 1;
                }
              }
            }
        });
      }
    }
    return std::make_pair(totalPlus, totalNumerals);
  }

  auto theoryComplexity(TypedTermList t) const 
  { return theoryComplexity(InequalityNormalizer::normalize(t)); }

  BY_INTERPRETED_KEY(TheoryComplexityAll,
      { return TotalComparableMultiset(lit.term().iterSummands()
          .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
          .collectStack()); })

  BY_INTERPRETED_KEY(TheoryComplexityMax,
      { return TotalComparableMultiset(self.maxAtomsNotLess(lit.term())
          .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
          .collectStack()); })

  BY_INTERPRETED_KEY(SizeAll,
      { return TotalComparableMultiset(lit.term().iterSummands()
          .map([&](auto x) { return x.atom().weight(); })
          .collectStack()); })

  BY_INTERPRETED_KEY(SizeMax,
      { return TotalComparableMultiset(self.maxAtomsNotLess(lit.term())
          .map([&](auto x) { return x.atom().weight(); })
          .collectStack()); })

  BY_INTERPRETED_KEY(NumberOfVarsAll,
      { return TotalComparableMultiset(lit.term().iterSummands()
          .map([&](auto x) { return x.atom().getDistinctVars(); })
          .collectStack()); })

  BY_INTERPRETED_KEY(NumberOfVarsMax,
      { return TotalComparableMultiset(self.maxAtomsNotLess(lit.term())
          .map([&](auto x) { return x.atom().getDistinctVars(); })
          .collectStack()); })

  template<class Cmp>
  auto getKey(TL::Token<Cmp> cmp, AlascaLiteralItpAny const& lit) const
  { return lit.apply([&](auto& lit) { return getKey(cmp, lit); }); }

  template<class Uninter, class FallBack, class Tup>
  Comparison compareItp(
      TL::Token<LiteralComparators::ALASCA::IfUninterpreted<Uninter, Tup, FallBack>> const& c, 
      AlascaLiteralItpAny const& l, AlascaLiteralItpAny const& r) const 
  { return compare(TL::Token<FallBack>{}, l, r); }

  template<class T>
  static Comparison compare(TotalComparableMultiset<T> const& l_, TotalComparableMultiset<T> const& r_)
  { 
    auto& l = l_._self;
    auto& r = r_._self;
    for (auto i : range(0, std::min(l.size(), r.size()))) {
      switch (compare(l[i], r[i])) {
        case Comparison::EQUAL: break;
        case Comparison::LESS: return Comparison::LESS;
        case Comparison::GREATER: return Comparison::GREATER;
      }
    }
    return Int::compare(l.size(), r.size());
  }

  template<class L, class R>
  static Comparison compare(std::pair<L, R> const& l, std::pair<L, R> const& r) 
  { 
    auto res = compare(l.first, r.first);
    return res == Comparison::EQUAL ? compare(l.second, r.second) : res;
  }

  template<class T>
  static Comparison compare(T const& l, T const& r) 
  { return Int::compare(l,r); }

  template<class Uninter, class FallBack, class Tup, class T, class... Ts>
  Comparison compareItp(
      TL::Token<LiteralComparators::ALASCA::IfUninterpreted<Uninter, Tup, FallBack>> cmp,
      AlascaLiteralItpAny const& l, AlascaLiteralItpAny const& r, T t, Ts... ts) const {
    auto res = [&]() {
      auto kl = getKey(t, l);
      auto kr = getKey(t, r);
      auto res = compare(kl, kr);
      return res != Comparison::EQUAL 
           ? res 
           : compareItp(cmp, l, r, std::move(ts)...);
    };
    switch (optionValue(t)) {
      case Options::AlascaSelectionMode::OFF: return Comparison::EQUAL;
      case Options::AlascaSelectionMode::ON: return res();
      case Options::AlascaSelectionMode::INV: return revert(res());
    }
    ASSERTION_VIOLATION
  }

  template<class Cmp>
  auto toCmpClosure(Cmp cmp_) const {
    return [this,cmp = std::move(cmp_)](auto const& l, auto const& r) -> bool
    { return this->compare(cmp, l, r) == Comparison::LESS; };
  }
};


 
struct AlascaSelectorDispatch {
  AlascaSelector const& self;

  template<unsigned i>
  RStack<__SelectedLiteral> computeSelected(TL::Token<GenericELiteralSelector<i>>, Clause* cl) 
  { throw UserErrorException("E literal selector not supported for alasca (yet)"); }

  template<unsigned i>
  RStack<__SelectedLiteral> computeSelected(TL::Token<GenericSpassLiteralSelector<i>>, Clause* cl) 
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
  { return iter
      .map([&](auto x) { x.setBGSelected(bgSelected); return x; })
      .collectRStack(); }

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
  RStack<__SelectedLiteral> computeSelected(TL::Token<CompleteBestLiteralSelector<QComparator>> token, Clause* cl) 
  {
    auto negative = iterSelectable(cl).collectRStack();
    negative->sort(AlascaComparator(self).toCmpClosure(TL::Token<LiteralComparators::Inverse<QComparator>>{}));
    if (negative->size() != 0) {
      return selectBG(negative[0]);
    } else {
      return selectMax(cl);
    }
  }

  template<class QComparator>
  RStack<__SelectedLiteral> computeSelected(TL::Token<BestLiteralSelector<QComparator>> token, Clause* cl) 
  { return selectBG(iterAll(cl, /*bgSelected*/ true)
      .maxBy(AlascaComparator(self).toCmpClosure(TL::Token<QComparator>{})).unwrap()); }

  template<bool complete>
  RStack<__SelectedLiteral> computeSelected(TL::Token<GenericLookaheadLiteralSelector<complete>>, Clause* cl) 
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
      .maxBy(AlascaComparator(self).toCmpClosure(TL::Token<LiteralComparators::LookaheadComparator>{}))
      .unwrap();

    return selectBG(best);
  } 


  template<bool complete>
  RStack<__SelectedLiteral> computeSelected(TL::Token<GenericRndLiteralSelector<complete>>, Clause* atoms) {
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


  RStack<__SelectedLiteral> computeSelected(TL::Token<MaximalLiteralSelector>, Clause* atoms) 
  { return selectMax(atoms); }

  RStack<__SelectedLiteral> computeSelected(TL::Token<TotalLiteralSelector>, Clause* cl) {
    return iterAll(cl, /* bgSelected */ true) .collectRStack();
  }
};


bool AlascaSelector::computeSelected(Clause* cl) const
{
  DEBUG(0, "     all atoms: ", *cl)
  if (cl->size() == 0) return false;
  auto selected = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, cl); });
  auto bg = selected[0].isBGSelected();
  for (auto x : *selected) {
    ASS_EQ(x.isBGSelected(), bg)
  }
  Recycled<Set<unsigned>> selIdx;
  RStack<Literal*> litUnsel;
  RStack<Literal*> litSel;
  for (auto l : *selected) {
    selIdx->insert(l.litIdx());
    litSel->push(l.literal());
  }
  for (unsigned i : range(0, cl->size())) {
    if (!selIdx->contains(i)) {
      litUnsel->push((*cl)[i]);
    }
  }
  cl->setSelected(litSel.size());
  for (auto i : range(0, litSel.size())) {
    (*cl)[i] = litSel[i];
  }

  for (auto i : range(0, litUnsel.size())) {
    (*cl)[litSel.size() + i] = litUnsel[i];
  }

  auto outputSelected = [&]() {
    return Output::catOwned(
        bg ? "BG-" : "",
      "selected: {",
      "[",
      arrayIter(*litSel).map([](auto* x) { return Output::ptr(x); }).output(", "),
      "]  ",
      arrayIter(*litUnsel).map([](auto* x) { return Output::ptr(x); }).output(", "),
      "}");
  };

#if VAMPIRE_CLAUSE_TRACING
  auto fwd = env.options->traceForward();
  if (fwd > 0 && unsigned(fwd) == cl->number()) {
    std::cout << "forward trace " << fwd << ": "
      << outputSelected()
      << std::endl;
  }
#endif
  DEBUG(0, "selected atoms: ", outputSelected())
  return bg;
}

bool AlascaSelector::getSelection(Clause* cl)
{
  if (auto out = _isBgSelected.tryGet(cl->number())) {
    return *out;
  } else {
    return _isBgSelected.insert(cl->number(), computeSelected(cl));
  } 
}

} // namespace Kernel
