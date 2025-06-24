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
struct AlascaAtomComparatorByLiteralKey { static constexpr bool enabled = false; };

#define BY_LITERAL_KEY(Type, body)                                                        \
  template<>                                                                              \
  struct AlascaAtomComparatorByLiteralKey<Type>                                           \
  {                                                                                       \
    static constexpr bool enabled = true;                                                 \
    template<class Self>                                                                  \
    static auto getLiteralKey(TL::Token<Type>, Self const& self, __SelectedLiteral const& x) \
    body                                                                                  \
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
struct NewAlascaAtomComparator {
  AlascaSelector const& self;

  NewAlascaAtomComparator(AlascaSelector const& self) : self(self) {}


  template<class C1, class C2>
  Comparison compare(TL::Token<LiteralComparators::Composite<C1, C2>>, __SelectedLiteral const& l, __SelectedLiteral const& r) const {
    auto res = compare(TL::Token<C1>{}, l, r);
    return res != Comparison::EQUAL ? res : compare(TL::Token<C2>{}, l, r);
  } 

  template<class C>
  Comparison compare(TL::Token<LiteralComparators::Inverse<C>>, __SelectedLiteral const& l, __SelectedLiteral const& r) const 
  { return compare(TL::Token<C>{}, r, l); } 


  // bool getLiteralKey(TL::Token<LiteralComparators::ColoredFirst>, __SelectedLiteral const& x) const 
  // { return x.literal()->color() != COLOR_TRANSPARENT; }
  //
  // bool getLiteralKey(TL::Token<LiteralComparators::NoPositiveEquality>, __SelectedLiteral const& x) const 
  // { return !(x.literal()->isEquality() && x.literal()->isPositive()); }
  //
  // bool getLiteralKey(TL::Token<LiteralComparators::Negative>, __SelectedLiteral const& x) const 
  //     // TODO this should be isNegativeForSelection (?)
  // { return x.literal()->isNegative(); }
  //
  // bool getLiteralKey(TL::Token<LiteralComparators::NegativeEquality>, __SelectedLiteral const& x) const 
  // { return x.literal()->isEquality() && x.literal()->isNegative(); }
  //
  // unsigned getLiteralKey(TL::Token<LiteralComparators::MaximalSize>, __SelectedLiteral const& x) const 
  // { return x.literal()->weight(); }
  //
  // int getLiteralKey(TL::Token<LiteralComparators::LeastVariables>, __SelectedLiteral const& x) const 
  // { return -int(x.literal()->numVarOccs()); }
  //
  // int getLiteralKey(TL::Token<LiteralComparators::LeastDistinctVariables>, __SelectedLiteral const& x) const 
  // { return -int(x.literal()->getDistinctVars()); }
  //
  // /* top level variables here does not mean alasca top level variables (e.g. x in `k x + t`), 
  //  * but mean variables that are arguments to the outer most function/predicate (e.g. x in `p(x, f(y))`) */
  // int getLiteralKey(TL::Token<LiteralComparators::LeastTopLevelVariables>, __SelectedLiteral const& x) const 
  // { return -int(anyArgIter(x.literal()).filter([](auto t) { return t.isVar(); }).count()); }

  template<class C, std::enable_if_t<AlascaAtomComparatorByLiteralKey<C>::enabled, bool> = true>
  Comparison compare(TL::Token<C> c, __SelectedLiteral const& l, __SelectedLiteral const& r) const  
  // { return Int::compare(getLiteralKey(c, l), getLiteralKey(c, r)); }
  { return Int::compare(
      AlascaAtomComparatorByLiteralKey<C>::getLiteralKey(c, self, l), 
      AlascaAtomComparatorByLiteralKey<C>::getLiteralKey(c, self, r)); }

  template<class T>
  Comparison compare(TL::Token<LiteralComparators::LexComparator>, T const& l, T const& r) const 
  { 
    // TODO this is not implemented as the LexComparator, as i don't think the lex comparator has any good semantic point to it, but is only there fore tie-breaking. this can be done way more cheaply
    return l == r ? Comparison::EQUAL
         : l < r ? Comparison::LESS
         : Comparison::GREATER;
  }

  // template<class T>
  // auto dbg(T const& x) 
  // { return "lex"; }

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

  template<class NumTraits>
  bool getKey(TL::Token<LiteralComparators::ALASCA::IsUwaConstraint>, AlascaLiteralItp<NumTraits> const& lit) const {
    // TODO
    return false;
  }

  template<class NumTraits>
  unsigned getKey(TL::Token<LiteralComparators::ALASCA::CntSummandsMax> const&, AlascaLiteralItp<NumTraits> const& lit) const 
  { return self.maxAtomsNotLessStack(lit.term()).size(); }

  template<class NumTraits>
  unsigned getKey(TL::Token<LiteralComparators::ALASCA::CntSummandsAll> const&, AlascaLiteralItp<NumTraits> const& lit) const 
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
  MultiSetUnsigned getKey(TL::Token<LiteralComparators::ALASCA::TheoryComplexityAll>, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(lit.term().iterSummands()
      .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(TL::Token<LiteralComparators::ALASCA::TheoryComplexityMax>, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(self.maxAtomsNotLess(lit.term())
      .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(TL::Token<LiteralComparators::ALASCA::SizeAll>, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(lit.term().iterSummands()
      .map([&](auto x) { return x.atom().weight(); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(TL::Token<LiteralComparators::ALASCA::SizeMax>, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(self.maxAtomsNotLess(lit.term())
      .map([&](auto x) { return x.atom().weight(); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(TL::Token<LiteralComparators::ALASCA::NumberOfVarsAll>, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(lit.term().iterSummands()
      .map([&](auto x) { return x.atom().getDistinctVars(); })
      .collectStack()); }

  template<class NumTraits>
  MultiSetUnsigned getKey(TL::Token<LiteralComparators::ALASCA::NumberOfVarsMax>, AlascaLiteralItp<NumTraits> const& lit) const 
  { return MultiSetUnsigned(self.maxAtomsNotLess(lit.term())
      .map([&](auto x) { return x.atom().getDistinctVars(); })
      .collectStack()); }

  template<class Cmp>
  auto getKey(TL::Token<Cmp> cmp, AlascaLiteralItpAny const& lit) const
  { return lit.apply([&](auto& lit) { return getKey(cmp, lit); }); }

  template<class Uninter, class FallBack, class Tup>
  Comparison compareItp(
      TL::Token<LiteralComparators::ALASCA::IfUninterpreted<Uninter, Tup, FallBack>> const& c, 
      AlascaLiteralItpAny const& l, AlascaLiteralItpAny const& r) const 
  { return compare(TL::Token<FallBack>{}, l, r); }

  static Comparison compare(bool const& l, bool const& r) 
  { return Int::compare(l,r); }

  static Comparison compare(unsigned const& l, unsigned const& r) 
  { return Int::compare(l,r); }

  template<class T>
  static Comparison compare(T const& l, T const& r);

  template<class T>
  Options::AlascaSelectionMode optionValue(T const&t) const;

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
  Stack<__SelectedLiteral> computeSelected(TL::Token<CompleteBestLiteralSelector<QComparator>> token, Clause* cl) 
  {
    auto negative = iterSelectable(cl).collectRStack();
    negative->sort(NewAlascaAtomComparator(self).toCmpClosure(TL::Token<QComparator>{}));
    if (negative->size() != 0) {
      return selectBG(negative[0]);
    } else {
      return selectMax(cl);
    }
  }

  template<class QComparator>
  Stack<__SelectedLiteral> computeSelected(TL::Token<BestLiteralSelector<QComparator>> token, Clause* cl) 
  { return selectBG(iterAll(cl, /*bgSelected*/ true)
      .maxBy(NewAlascaAtomComparator(self).toCmpClosure(TL::Token<QComparator>{})).unwrap()); }

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
      .maxBy(NewAlascaAtomComparator(self).toCmpClosure(TL::Token<LiteralComparators::LookaheadComparator>{}))
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
