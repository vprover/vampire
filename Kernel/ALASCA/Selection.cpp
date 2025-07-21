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

#define ENABLE_DEBUG_KEYS 1

#if ENABLE_DEBUG_KEYS

#  define DEBUG_KEYS(name, input, body)                                                   \
    {                                                                                     \
      auto __result = [&]() { body }();                                                   \
      DBG(name, "(", Output::ptr(input), ") = ", __result);                               \
      return __result;                                                                    \
    }                                                                                     \

#else

#  define DEBUG_KEYS(name, input, body)                                                   \
   { body }                                                                               \

#endif //  ENABLE_DEBUG_KEYS

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
    static auto getKey(TL::Token<Type>, Self const& self, Literal* lit)                   \
     DEBUG_KEYS(#Type, lit, body)                                                         \
  };                                                                                      \

BY_LITERAL_KEY(LiteralComparators::ColoredFirst, 
  { return lit->color() != COLOR_TRANSPARENT; })

BY_LITERAL_KEY(LiteralComparators::NoPositiveEquality, 
  { return !(lit->isEquality() && lit->isPositive()); })

// TODO this should be isNegativeForSelection (?)
BY_LITERAL_KEY(LiteralComparators::Negative, 
  { return lit->isNegative(); })

BY_LITERAL_KEY(LiteralComparators::NegativeEquality, 
  { return lit->isEquality() && lit->isNegative(); })

BY_LITERAL_KEY(LiteralComparators::MaximalSize, 
  { return lit->weight(); })

BY_LITERAL_KEY(LiteralComparators::LeastVariables, 
  { return -int(lit->numVarOccs()); })

BY_LITERAL_KEY(LiteralComparators::LeastDistinctVariables, 
  { return -int(lit->getDistinctVars()); })

  /* top level variables here does not mean alasca top level variables (e.g. x in `k x + t`), 
   * but mean variables that are arguments to the outer most function/predicate (e.g. x in `p(x, f(y))`) */
BY_LITERAL_KEY(LiteralComparators::LeastTopLevelVariables,
  { return -int(anyArgIter(lit).filter([](auto t) { return t.isVar(); }).count()); })


#define DEBUG(lvl, ...) if (lvl < 0) { DBG(__VA_ARGS__) }
struct AlascaComparator {
  AlascaSelector const& self;
  Clause* cl;

  AlascaComparator(AlascaSelector const& self, Clause* cl) : self(self), cl(cl) {}

  Literal* lit(unsigned i) const { return (*cl)[i]; }

  template<class C1, class C2>
  Comparison compare(TL::Token<LiteralComparators::Composite<C1, C2>>, unsigned const& l, unsigned const& r) const {
    auto res = compare(TL::Token<C1>{}, l, r);
    return res != Comparison::EQUAL ? res : compare(TL::Token<C2>{}, l, r);
  } 

  template<class C>
  Comparison compare(TL::Token<LiteralComparators::Inverse<C>>, unsigned const& l, unsigned const& r) const 
  { return compare(TL::Token<C>{}, r, l); } 

  template<class C, std::enable_if_t<AlascaComparatorByLiteralKey<C>::enabled, bool> = true>
  Comparison compare(TL::Token<C> c, unsigned const& l, unsigned const& r) const  
  { return Int::compare(
      AlascaComparatorByLiteralKey<C>::getKey(c, self, lit(l)), 
      AlascaComparatorByLiteralKey<C>::getKey(c, self, lit(r))); }

  template<class T>
  Comparison compare(TL::Token<LiteralComparators::LexComparator>, T const& l, T const& r) const 
  { 
    // TODO this is not implemented as the LexComparator, as i don't think the lex comparator has any good semantic point to it, but is only there fore tie-breaking. this can be done way more cheaply
    return l == r ? Comparison::EQUAL
         : l < r ? Comparison::LESS
         : Comparison::GREATER;
  }

  template<class FallBack, class... Inter>
  Comparison compare(TL::Token<LiteralComparators::ALASCA::Comparator<std::tuple<Inter...>, FallBack>> c, unsigned const& l, unsigned const& r) const 
  { 
    auto norml = InequalityNormalizer::normalize(lit(l));
    auto normr = InequalityNormalizer::normalize(lit(r));
    return compareItp(c, norml, normr, TL::Token<Inter>{}...);
  }

#define BY_INTERPRETED_KEY(Type, clsrLit, clsrItp)                                        \
  auto getKey(TL::Token<LiteralComparators::ALASCA::Type>, Literal* lit) const            \
  DEBUG_KEYS(#Type, lit, return clsrLit(lit);)                                            \
                                                                                          \
  template<class NumTraits>                                                               \
  auto getKey(TL::Token<LiteralComparators::ALASCA::Type>, AlascaLiteralItp<NumTraits> const& lit) const \
  DEBUG_KEYS(#Type, lit, return clsrItp(lit);)                                            \
                                                                                          \
  Options::AlascaSelectionMode optionValue(TL::Token<LiteralComparators::ALASCA::Type>) const { \
    static Options::AlascaSelectionMode val = env.options->alascaSelection ## Type();     \
    return val;                                                                           \
  }                                                                                       \


  auto maxEqTermsArray(Literal* lit) const {
    using Out = SmallArray<TermList, 2>;
    ASS(lit->isEquality())
    switch (self.ord->getEqualityArgumentOrder(lit)) {
      case Ordering::Result::EQUAL: return Out::fromItems();
      case Ordering::Result::LESS: return Out::fromItems(lit->termArg(1));
      case Ordering::Result::GREATER: return Out::fromItems(lit->termArg(0));
      case Ordering::Result::INCOMPARABLE: return Out::fromItems(
          lit->termArg(0),
          lit->termArg(1)
         );
    }
    ASSERTION_VIOLATION
  }

  auto maxEqTerms(Literal* lit) const { return arrayIter(maxEqTermsArray(lit)); }
  auto maxEqTermsTyped(Literal* lit) const { 
    return maxEqTerms(lit)
      .map([lit](TermList t) { return TypedTermList(t, lit->eqArgSort()); });

  }

  BY_INTERPRETED_KEY(IsUwaConstraint,
    [&](Literal* lit) -> bool { return false; },
    [&](auto& lit) -> bool {
      // TODO ?
      return lit.symbol() == AlascaPredicate::NEQ;
    })

  BY_INTERPRETED_KEY(NumberOfMaxAtoms,
    [&](Literal* lit) -> unsigned { 
      if (lit->isEquality()) {
        switch (self.ord->getEqualityArgumentOrder(lit)) {
          case Ordering::Result::EQUAL: return 0;
          case Ordering::Result::LESS: return 1;
          case Ordering::Result::GREATER: return 1;
          case Ordering::Result::INCOMPARABLE: return 2;
        }
      } else {
        return 1;
      }
    },
    [&](auto& lit) -> unsigned 
    { return self.maxAtomsNotLessStack(lit.term()).size(); })

  BY_INTERPRETED_KEY(NumberOfAllAtoms, 
    [&](Literal* lit) -> unsigned { 
      if (lit->isEquality()) {
        return 2;
      } else {
        return 1;
      }
    }, 
    [&](auto& lit) -> unsigned 
    { return lit.term().nSummands(); })

  unsigned theoryComplexity(AnyAlascaTerm t) const {
    // unsigned totalNumerals = 0;
    unsigned totalPlus     = 0;
    for (auto t : t.bottomUpIter()) {
      if (auto sum = t.asSum()) {
        sum->apply([&](auto& sum) {
            if (sum.nSummands() == 0) {
              // totalNumerals += 1;
            } else {
              totalPlus += sum.nSummands() - 1;
              // for (auto monom : sum.iterSummands()) {
              //   if (monom.numeral() != 1) {
              //     totalNumerals += 1;
              //   }
              // }
            }
        });
      }
    }
    return totalPlus;
    // return std::make_pair(totalPlus, totalNumerals);
  }

  auto theoryComplexity(TypedTermList t) const 
  { return theoryComplexity(InequalityNormalizer::normalize(t)); }

  BY_INTERPRETED_KEY(TheoryComplexityOfAllAtoms,
    [&](Literal* lit) -> int {
      return -int(termArgIterTyped(lit)
                .map([&](auto x) { return theoryComplexity(x); })
                .sum());
    },
    [&](auto& lit) -> int { 
      return -int(lit.term().iterSummands()
        .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
        .sum()); 
    })

  BY_INTERPRETED_KEY(TheoryComplexityOfMaxAtoms,
    [&](Literal* lit) -> int {
      if (lit->isEquality()) {
        return -int(maxEqTermsTyped(lit)
                  .map([&](auto x) { return theoryComplexity(x); })
                  .sum());
      } else {
        return -int(termArgIterTyped(lit)
                  .map([&](auto x) { return theoryComplexity(x); })
                  .sum());
      }
    },
    [&](auto& lit) -> int { 
      return -int(self.maxAtomsNotLess(lit.term())
          .map([&](auto x) { return theoryComplexity(TypedTermList(x.atom(), NumTraits::sort())); })
          .sum()); 
    })

  BY_INTERPRETED_KEY(SizeOfAllAtoms,
    [&](Literal* lit) {
      if (lit->isEquality()) {
        return anyArgIter(lit)
                  .map([](auto x) { return x.weight(); })
                  .sum();
      } else {
        return lit->weight();
      }
    },
      [&](auto& lit){ return lit.term().iterSummands()
          .map([&](auto x) { return x.atom().weight(); })
          .sum(); })

  BY_INTERPRETED_KEY(SizeOfMaxAtoms,
    [&](Literal* lit) {
      if (lit->isEquality()) {
        return maxEqTerms(lit)
                  .map([](auto x) { return x.weight(); })
                  .sum();
      } else {
        return anyArgIter(lit)
                  .map([](auto x) { return x.weight(); })
                  .sum();
      }
    },
    [&](auto& lit){ 
      return self.maxAtomsNotLess(lit.term())
        .map([&](auto x) { return x.atom().weight(); })
        .sum(); 
     })

  // unif prob with ground terms
  //   size(t) - distinctVars(t)
  unsigned probPowers(TermList t) const { return t.weight() - t.getDistinctVars(); }
  unsigned probPowers(Literal* l) const { return l->weight() - l->getDistinctVars(); }


  // unif prob:
  //   min(vars * (1/signatureSize)^(termSize - 1))
  //
  //   <-> min(log(vars * (1/signatureSize)^(termSize - 1)))
  //   <-> min(log(vars) + log(1/signatureSize) * (termSize - 1))
  //   <-> min(log(vars) +  -log(signatureSize) * (termSize - 1))
  double logProbability(TermList t) const {
    return log(double(t.getDistinctVars())) 
         - log(double(env.signature->functions())) * (double(t.weight()) - 1);
  }

  double logProbability(Literal* t) const {
    return log(double(t->getDistinctVars())) 
         - log(double(env.signature->functions())) * (double(t->weight()) - 2) 
         - log(double(env.signature->predicates())) ;
  }

  // unif prob:
  //   min(vars * (1/signatureSize)^(termSize - 1))
  //
  //   <-> min(log(vars * (1/signatureSize)^(termSize - 1)))
  //   <-> min(log(vars) + log(1/signatureSize) * (termSize - 1))
  //   <-> min(log(vars) +  -log(signatureSize) * (termSize - 1))

  BY_INTERPRETED_KEY(LogUnifProbabilityOfAllAtoms,
    [&](Literal* lit) {
      if (lit->isEquality()) {
        return anyArgIter(lit)
          .map([&](TermList t) { return probPowers(t); })
          .sum();
      } else {
        return probPowers(lit);
      }
    },
    [&](auto& lit){ 
      return lit.term().iterSummands()
          .map([&](auto x) { return probPowers(x.atom()); })
          .sum();
    })

  BY_INTERPRETED_KEY(LogUnifProbabilityOfMaxAtoms,
    [&](Literal* lit) {
      if (lit->isEquality()) {
        return maxEqTerms(lit)
          .map([&](TermList t) { return probPowers(t); })
          .sum();
      } else {
        return probPowers(lit);
      }
    },
    [&](auto& lit){ 
      return self.maxAtomsNotLess(lit.term())
          .map([&](auto x) { return probPowers(x.atom()); })
          .sum();
    })

  template<class Cmp>
  auto getKey(TL::Token<Cmp> cmp, AlascaLiteral const& lit) const
  { 
    auto itp = lit.asItp();
    if (itp.isSome()) {
      return itp->apply([&](auto& lit) { return getKey(cmp, lit); });
    } else {
      return getKey(cmp, lit.toLiteral());
    }
  }

  template<class FallBack, class Tup>
  Comparison compareItp(
      TL::Token<LiteralComparators::ALASCA::Comparator<Tup, FallBack>> const& c, 
      AlascaLiteral const& l, AlascaLiteral const& r) const 
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

  template<class FallBack, class Tup, class T, class... Ts>
  Comparison compareItp(
      TL::Token<LiteralComparators::ALASCA::Comparator<Tup, FallBack>> cmp,
      AlascaLiteral const& l, AlascaLiteral const& r, T t, Ts... ts) const {
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

  using ComputeSelectedResult = std::pair<bool, RStack<unsigned>>;
  template<unsigned i>
  ComputeSelectedResult computeSelected(TL::Token<GenericELiteralSelector<i>>, Clause* cl) 
  { throw UserErrorException("E literal selector not supported for alasca (yet)"); }

  template<unsigned i>
  ComputeSelectedResult computeSelected(TL::Token<GenericSpassLiteralSelector<i>>, Clause* cl) 
  { throw UserErrorException("Spass literal selector not supported for alasca (yet)"); }

  auto iterMaxLitIndices(Clause* const& atoms) const 
  { 
     return OrderingUtils::maxElems(atoms->size(),
                    [=](unsigned l, unsigned r)
                    { return AlascaOrderingUtils::compareAtom(self.ord, (*atoms)[l], (*atoms)[r]); },
                    [&](unsigned i)
                    { return (*atoms)[i]; },
                    SelectionCriterion::NOT_LESS);
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

  auto iterSelectableIndices(Clause* cl) const
  { 
    return range(0, cl->size())
      .filter([this,cl](auto i) 
          { return selectable(InequalityNormalizer::normalize((*cl)[i])); });
  }

  static auto iterAllIndices(Clause* cl) { return range(0, cl->size()); }

  auto selectMax(Clause* const& atoms) const 
  { return std::make_pair(/* bg selected */ false, iterMaxLitIndices(atoms).collectRStack()); }

  auto selectBG(unsigned idx) const 
  { return std::make_pair(/* bg selected */ true, iterItems(idx).collectRStack()); }

  // TODO create another complete best selector that selects first the best unproductive ones and then the best productive ones

  template<class QComparator>
  auto computeSelected(TL::Token<CompleteBestLiteralSelector<QComparator>> token, Clause* cl) 
  {
    auto negative = iterSelectableIndices(cl).collectRStack();
    negative->sort(AlascaComparator(self, cl).toCmpClosure(TL::Token<LiteralComparators::Inverse<QComparator>>{}));
    if (negative->size() != 0) {
      return selectBG(negative[0]);
    } else {
      return selectMax(cl);
    }
  }

  template<class QComparator>
  auto computeSelected(TL::Token<BestLiteralSelector<QComparator>> token, Clause* cl) 
  { return selectBG(range(0,cl->size())
      .maxBy(AlascaComparator(self, cl).toCmpClosure(TL::Token<QComparator>{})).unwrap()); }

  template<bool complete>
  auto computeSelected(TL::Token<GenericLookaheadLiteralSelector<complete>>, Clause* cl) 
  {
    ASS_REP(self._inf, "inference engine must be set when using lookahead selection")

    RStack<unsigned> leastResults;
    auto selectable = complete 
      ? iterSelectableIndices(cl).collectRStack()
      : iterAllIndices(cl).collectRStack();

    auto gens = arrayIter(*selectable)
      .map([&](auto lit) { return self._inf->lookaheadResultEstimation(__SelectedLiteral(cl, lit, /* bgSelected */ true)); })
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
      .maxBy(AlascaComparator(self, cl).toCmpClosure(TL::Token<LiteralComparators::LookaheadComparator>{}))
      .unwrap();

    return selectBG(best);
  }


  template<bool complete>
  auto computeSelected(TL::Token<GenericRndLiteralSelector<complete>>, Clause* cl) {
    if (complete) {
      RStack<unsigned> selectable;
      selectable->loadFromIterator(iterSelectableIndices(cl));
      if (selectable.size() != 0
          // && Random::getBit() // <- sometimes select all maximals even if there is selectable TODO do we want this really?
          ) {
        return selectBG(Random::getElem(*selectable));
      } else {
        return selectMax(cl);
      }
    } else {
      return selectBG(Random::getInteger(cl->size()));
    }
  }


  auto computeSelected(TL::Token<MaximalLiteralSelector>, Clause* atoms) 
  { return selectMax(atoms); }

  auto computeSelected(TL::Token<TotalLiteralSelector>, Clause* cl) {
    return std::make_pair(/* bgSelected */ true, iterAllIndices(cl).collectRStack());
  }
};


bool AlascaSelector::computeSelected(Clause* cl) const
{
  DEBUG(0, "     all atoms: ", *cl)
  if (cl->size() == 0) return false;
  auto [bg, selectedLits] = _mode.apply([&](auto token) { return AlascaSelectorDispatch{*this}.computeSelected(token, cl); });
  auto bgSelected = bg;
  Recycled<Set<unsigned>> selIdx;
  RStack<Literal*> litUnsel;
  RStack<Literal*> litSel;
  for (auto i : *selectedLits) {
    selIdx->insert(i);
    litSel->push((*cl)[i]);
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
  cl->notifyLiteralReorder();

  auto outputSelected = [&]() {
    return Output::catOwned(
        bgSelected ? "BG-" : "",
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
