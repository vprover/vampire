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
 * @file BinInf.hpp
 * Defines class BinInf
 *
 */

#ifndef __ALASCA_Inferences_BinInf__
#define __ALASCA_Inferences_BinInf__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/ALASCA/Ordering.hpp"
#include "Kernel/UnificationWithAbstraction.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Reflection.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Shell/Options.hpp"
#include "Lib/TypeList.hpp"
#include <type_traits>
#include <utility>

#define DEBUG(lvl, ...)  if (lvl < 0) { DBG(__VA_ARGS__) }
namespace TL = Lib::TypeList;

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

 
template<class Inner>
void attachToInner(Inner& inner, SaturationAlgorithm* salg) { }

// TODO rename to ApplicabilityChecks

namespace ApplicabilityCheck {

template<bool B>
struct Constant {
  template<class Selected, class FailLogger>
  bool checkBeforeUnif(Selected selected, Ordering* ord, FailLogger logger) { return B; }

  template<class Selected, class FailLogger>
  bool checkAfterUnif(Selected selected, Ordering* ord, AbstractingUnifier& unif, FailLogger logger) { return B; }

  friend std::ostream& operator<<(std::ostream& out, Constant const& self)
  { return out << B; }
};


struct TermMaximalityConstraint {
  OrderingUtils::SelectionCriterion max;
  /* whether the term must be wrt all atomic terms in the clause, or wrt all atomic terms in its literal.
   * e.g. consider the clause f(a) + a > 0 \/ f(f(a)) + a > 0,
   * here the occurence of f(a) is locally maximal, but not globally, while f(f(a)) is both locally and 
   * globally maximal */
  bool local;

  static constexpr unsigned checkForNArgs(unsigned arity) { return arity == 1; }

  template<class Selected, class FailLogger>
  bool checkBeforeUnif(Selected selected, Ordering* ord, FailLogger logger) {
    // TODO
    return true; 
  }

  template<class Selected, class FailLogger>
  bool checkAfterUnif(Selected sel_bank, Ordering* ord, AbstractingUnifier& unif, FailLogger logger) {
    auto log = [&](auto msg) { logger(Output::cat("atom not maximal: ", msg)); };
    auto* selected = sel_bank.first;
    auto varBank = sel_bank.second;
    return local ? AlascaOrderingUtils ::atomLocalMaxAfterUnif(ord, *selected, max, unif, varBank, log)
                 : AlascaOrderingUtils::atomGlobalMaxAfterUnif(ord, *selected, max, unif, varBank, log);
  }


  friend std::ostream& operator<<(std::ostream& out, TermMaximalityConstraint const& self)
  { return out << "term" << "(" << self.max << ", " << (self.local ? "local" : "global") << ")"; }
};

struct LiteralMaximalityConstraint {
  OrderingUtils::SelectionCriterion max;

  static constexpr unsigned checkForNArgs(unsigned arity) { return arity == 1; }

  template<class Selected, class FailLogger>
  bool checkBeforeUnif(std::pair<Selected const*, unsigned> selected,  FailLogger logger) {
    // TODO
    return true; 
  }

  template<class Selected, class FailLogger>
  bool checkAfterUnif(std::pair<Selected const*, unsigned>  sel_bank, Ordering* ord, AbstractingUnifier& unif, FailLogger logger) {
    auto* selected = sel_bank.first;
    auto varBank = sel_bank.second;
    return AlascaOrderingUtils::litMaxAfterUnif(ord, *selected, max, unif, varBank, 
             [&](auto msg) { logger(Output::cat("literal not maximal: ", msg)); });
  }

  friend std::ostream& operator<<(std::ostream& out, LiteralMaximalityConstraint const& self)
  { return out << "literal" << "(" << self.max << ")"; }
};


template<unsigned N, class C>
struct PremiseN {
  C check;
  PremiseN(C check) : check(std::move(check)) {}

  static constexpr unsigned checkForNArgs(unsigned arity) { return arity == 1; }

  template<class Logger>
  static auto wrapLogger(Logger& logger) 
  { return [&](auto msg) { logger(Output::cat("premise ", N, ": ", msg)); }; }

  template<class Tup, class FailLogger>
  bool checkBeforeUnif(Tup tup,  FailLogger logger) 
  { return check.checkBeforeUnif(std::get<N>(tup), wrapLogger(logger)); }

  template<class Tup, class FailLogger>
  bool checkAfterUnif(Tup tup, Ordering* ord, AbstractingUnifier& unif, FailLogger logger) 
  { return check.checkAfterUnif(std::get<N>(tup), ord, unif, wrapLogger(logger)); }

  friend std::ostream& operator<<(std::ostream& out, PremiseN const& self)
  { return out << "premise" << N << "(" << self.check << ")"; }
};

template<unsigned n, class C>
PremiseN<n, C> premiseN(C check) 
{ return PremiseN<n, C>(std::move(check)); }


template<unsigned L, unsigned R>
struct CmpLitLit {
  OrderingUtils::SelectionCriterion max;

  static constexpr unsigned checkForNArgs(unsigned arity) { return arity == 1; }

  template<class Tup, class FailLogger>
  bool checkBeforeUnif(Tup tup,  FailLogger logger) {
    // TODO
    return true; 
  }

  template<class Tup, class FailLogger>
  bool checkAfterUnif(Tup  tup, Ordering* ord, AbstractingUnifier& unif, FailLogger logger) {
    auto lhs_bank = std::get<L>(tup);
    auto rhs_bank = std::get<R>(tup);
    auto lσ = unif.subs().apply(lhs_bank.first->literal(), lhs_bank.second);
    auto rσ = unif.subs().apply(rhs_bank.first->literal(), rhs_bank.second);
    auto res = ord->compare(lσ, rσ);
    if (OrderingUtils::isTrue(max, res)) {
      return true;
    } else {
      logger(Output::cat("main literal comparison: L", L, " ", res, " L", R, " ", 
          ": ", lσ, " ", res, " ", rσ, " (expected: ", max, ")"));
      return false;
    }
  }

  friend std::ostream& operator<<(std::ostream& out, CmpLitLit const& self)
  { return out << "L" << L << " " << self.max << " L" << R; }
};


struct BGSelected {
  OrderingUtils::SelectionCriterion max;

  static constexpr unsigned checkForNArgs(unsigned arity) { return arity == 1; }

  template<class Selected, class FailLogger>
  bool checkBeforeUnif(std::pair<Selected const*, unsigned> sel_bank, Ordering* ord, FailLogger logger) 
  { return sel_bank.first->isBGSelected(); }

  template<class Selected, class FailLogger>
  bool checkAfterUnif(std::pair<Selected const*, unsigned> sel_bank, Ordering* ord, AbstractingUnifier& unif, FailLogger logger) 
  { 
    if (sel_bank.first->isBGSelected()) {
      return true;
    } else {
      logger(Output::cat(*sel_bank.first, " is not BG-selected"));
      return false;
    }
  }

  friend std::ostream& operator<<(std::ostream& out, BGSelected const& self)
  { return out << "BG-selected"; }
};

template<class A, class B>
struct Or {
  A lhs;
  B rhs;

  static constexpr unsigned checkForNArgs(unsigned arity) { return true; }

  Or(A a, B b) : lhs(std::move(a)), rhs(std::move(b)) { }

  template<class Selected, class FailLogger>
  bool checkBeforeUnif(Selected selected, Ordering* ord, FailLogger logger) 
  { std::string lhsMsg;
    return lhs.checkBeforeUnif(selected, ord, [&](auto msg) { lhsMsg = Output::toString(msg); })
        || rhs.checkBeforeUnif(selected, ord, [&](auto msg) { logger(Output::cat(lhsMsg, " and ", msg)); }); }

  template<class Selected, class FailLogger>
  bool checkAfterUnif(Selected selected, Ordering* ord, AbstractingUnifier& unif, FailLogger logger)
  { std::string lhsMsg;
    return lhs.checkAfterUnif(selected, ord, unif, [&](auto msg) { lhsMsg = Output::toString(msg); })
        || rhs.checkAfterUnif(selected, ord, unif, [&](auto msg) { logger(Output::cat(lhsMsg, " and ", msg)); }); }

  friend std::ostream& operator<<(std::ostream& out, Or const& self)
  { return out << "(" << self.lhs << " or " << self.rhs << ")"; }
};

template<class A, class B>
Or(A,B) -> Or<A,B>;

template<class A1>
auto any(A1 a1) { return a1; }

template<class A1, class A2, class... As>
auto any(A1 a1, A2 a2, As... as)
{ return Or(a1, any(a2, as...)); }

template<class A, class B>
struct And {
  A lhs;
  B rhs;

  And(A a, B b) : lhs(std::move(a)), rhs(std::move(b)) { }

  template<class Selected, class FailLogger>
  bool checkBeforeUnif(Selected selected, Ordering* ord, FailLogger logger) 
  { return lhs.checkBeforeUnif(selected, ord, [&](auto msg) { logger(msg); })
        && rhs.checkBeforeUnif(selected, ord, [&](auto msg) { logger(msg); }); }

  template<class Selected, class FailLogger>
  bool checkAfterUnif(Selected selected, Ordering* ord, AbstractingUnifier& unif, FailLogger logger)
  { return lhs.checkAfterUnif(selected, ord, unif, [&](auto msg) { logger(msg); })
        && rhs.checkAfterUnif(selected, ord, unif, [&](auto msg) { logger(msg); }); }

  friend std::ostream& operator<<(std::ostream& out, And const& self)
  { return out << "(" << self.lhs << " and " << self.rhs << ")"; }
};

template<class A, class B>
And(A,B) -> And<A,B>;

template<class A1>
auto all(A1 a1) { return a1; }

template<class A1, class A2, class... As>
auto all(A1 a1, A2 a2, As... as)
{ return And(a1, all(a2, as...)); }

} // namespace ApplicabilityCheck

template <typename T, typename = void>
struct has_atomicTermMaximality : std::false_type {};
template <typename T>
struct has_atomicTermMaximality<T, std::void_t<decltype(std::declval<T>().localAtomicTermMaximality())>> : std::true_type {};


template<class C, std::enable_if_t<has_atomicTermMaximality<C>::value, bool> = true>
static auto binInfApplicabilityChecks(C const& c) {
  return ApplicabilityCheck::all(
      ApplicabilityCheck::any(
        ApplicabilityCheck::BGSelected{},
        ApplicabilityCheck::all(
          ApplicabilityCheck::LiteralMaximalityConstraint { .max = c.literalMaximality(), },
          ApplicabilityCheck::TermMaximalityConstraint { .max = c.globalAtomicTermMaximality(), .local = false, }
        )
      ),
      ApplicabilityCheck::TermMaximalityConstraint { .max = c.localAtomicTermMaximality() , .local = true, }
  );
}


template<class C, std::enable_if_t<!has_atomicTermMaximality<C>::value, bool> = true>
static auto binInfApplicabilityChecks(C const& c) {
  return ApplicabilityCheck::all(
      ApplicabilityCheck::any(
        ApplicabilityCheck::BGSelected{},
        ApplicabilityCheck::LiteralMaximalityConstraint { .max = c.literalMaximality(), }
      )
  );
}

template<class Prem, class FailLogger>
bool binInfPreUnificationCheck(Prem const& prem, Ordering* ord, FailLogger logger) 
{ 
  using VarBanks  = Indexing::RetrievalAlgorithms::DefaultVarBanks;
  auto empty = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
  return binInfApplicabilityChecks(prem)
    .checkAfterUnif(std::make_pair(&prem, VarBanks::query), ord, empty, logger);
}


 
template<class Rule>
struct BinInf
: public GeneratingInferenceEngine
{
  using Lhs = typename Rule::Lhs;
  using Rhs = typename Rule::Rhs;
  using Key = KeyType<Lhs>;
  static_assert(std::is_same_v<KeyType<Lhs>, KeyType<Rhs>>);
private:
  std::shared_ptr<AlascaState> _shared;
  Rule _rule;
  AlascaIndex<Lhs>* _lhs;
  AlascaIndex<Rhs>* _rhs;
public:
  USE_ALLOCATOR(BinInf);

  BinInf(BinInf&&) = default;
  BinInf(std::shared_ptr<AlascaState> shared, Rule rule)
    : _shared(std::move(shared))
    , _rule(std::move(rule))
    , _lhs(nullptr)
    , _rhs(nullptr)
  {  }


  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override
  {
    auto unif_ = std::unique_ptr<AbstractingUnifier>(move_to_heap(AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF))));
    auto* unif = unif_.get();

    return pvi(concatIters(
      dropElementType(Lhs::iter(*_shared, selection)
        .flatMap([=](auto lhs) { 
          ASS_REP(unif->isEmpty(), *unif) 
          return _rhs->template find<VarBanks>(unif, lhs.key()); 
        })),
      dropElementType(Rhs::iter(*_shared, selection)
        .flatMap([=](auto rhs) { 
          ASS_REP(unif->isEmpty(), *unif)
          return _lhs->template find<VarBanks>(unif, rhs.key()); 
        }))
      ).store(std::move(unif_)));
  }

  void attach(SaturationAlgorithm* salg) final override
  { 
    ASS(!_rhs);
    ASS(!_lhs);

    GeneratingInferenceEngine::attach(salg);

    _lhs=static_cast<decltype(_lhs)> (_salg->getIndexManager()->request(Lhs::indexType()));
    _rhs=static_cast<decltype(_rhs)>(_salg->getIndexManager()->request(Rhs::indexType()));

    _lhs->setShared(_shared);
    _rhs->setShared(_shared);

    attachToInner(_rule, salg);
  }

  void detach() final override {
    ASS(_salg);
    _lhs = nullptr;
    _rhs = nullptr;
    _salg->getIndexManager()->release(Lhs::indexType());
    _salg->getIndexManager()->release(Rhs::indexType());
    GeneratingInferenceEngine::detach();
  }

  using VarBanks  = Indexing::RetrievalAlgorithms::DefaultVarBanks;

  template <typename T, typename = void>
  struct has_binApplicabilityChecks : std::false_type {};
  template <typename T>
  struct has_binApplicabilityChecks<T, 
    std::void_t<decltype(std::declval<T const&>().binApplicabilityChecks(std::declval<Lhs const&>(), std::declval<Rhs const&>()))>> : std::true_type {};


  template<class R, class Lhs, class Rhs, 
    std::enable_if_t< has_binApplicabilityChecks<R>::value, bool> = true>
  static auto binApplicabilityChecks(R const& rule, Lhs const& lhs, Rhs const& rhs) 
  { return rule.binApplicabilityChecks(lhs,rhs); }

  template<class R, class Lhs, class Rhs, 
    std::enable_if_t<!has_binApplicabilityChecks<R>::value, bool> = true>
  static auto binApplicabilityChecks(R const& rule, Lhs const& lhs, Rhs const& rhs) 
  { return ApplicabilityCheck::Constant<true>{}; }

  template<class Prem, class FailLogger>
  bool binInfPreUnificationCheck(Prem const& prem, FailLogger logger) 
  { 
    auto empty = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
    return binInfApplicabilityChecks(prem)
      .checkAfterUnif(std::make_pair(&prem, VarBanks::query), _shared->ordering, empty, logger);
  }


  template<class FailLogger>
  bool postUnificationCheck(Lhs const& lhs, unsigned lhsVarBank, 
                            Rhs const& rhs, unsigned rhsVarBank,
                            AbstractingUnifier& unif,
                            FailLogger logger) 
  { 
    namespace Check = ApplicabilityCheck;
    auto prems = std::make_tuple(std::make_pair(&lhs, lhsVarBank),
                                 std::make_pair(&rhs, rhsVarBank));
    auto check = Check::all(
        Check::premiseN<0>(binInfApplicabilityChecks(lhs)),
        Check::premiseN<1>(binInfApplicabilityChecks(rhs)),
        binApplicabilityChecks(_rule, lhs, rhs)
        );
    return check.checkAfterUnif(prems, _shared->ordering, unif, logger);
  }

  ClauseIterator generateClauses(Clause* premise) final override
  {
    ASS(_lhs)
    ASS(_rhs)
    ASS(_shared)

    // TODO get rid of stack
    Stack<Clause*> out;

    auto sigma = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
    ASS(sigma.isEmpty())


    DEBUG(0, _rule.name())
    for (auto const& lhs : Lhs::iter(*_shared, premise)) {
      if (!binInfPreUnificationCheck(lhs, [](auto&& msg) { DEBUG(2, "no lhs: ", msg); })) 
        continue;
      DEBUG(0, "lhs: ", lhs, " (", lhs.clause()->number(), ")")
      for (auto rhs_sigma : _rhs->template find<VarBanks>(&sigma, lhs.key())) {
        auto& rhs   = *rhs_sigma.data;
        DEBUG(0, "  rhs: ", rhs, " (", rhs.clause()->number(), ")")
        DEBUG(0, "  sigma: ", sigma)
        auto check = postUnificationCheck(lhs, VarBanks::query, 
                                          rhs, VarBanks::internal, sigma, 
                                          [](auto&& msg) { DEBUG(1, "    no result: ", msg) });
        if (check) {
          for (Clause* res : iterTraits(_rule.applyRule(lhs, VarBanks::query, rhs, VarBanks::internal, sigma))) {
            DEBUG(0, "    result: ", *res)
            out.push(res);
          }
          DEBUG(0, "")
        }
      }
    }

    ASS_REP(sigma.isEmpty(), sigma)

    for (auto const& rhs : Rhs::iter(*_shared, premise)) {
      if (!binInfPreUnificationCheck(rhs, [](auto&& msg) { DEBUG(2, "no rhs: ", msg); })) 
        continue;
      DEBUG(0, "rhs: ", rhs, " (", rhs.clause()->number(), ")")
      for (auto lhs_sigma : _lhs->template find<VarBanks>(&sigma, rhs.key())) {
        auto& lhs   = *lhs_sigma.data;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(0, "  lhs: ", lhs, " (", lhs.clause()->number(), ")")
          DEBUG(0, "  sigma: ", sigma)
          auto check = postUnificationCheck(lhs, VarBanks::internal, 
                                            rhs, VarBanks::query, sigma, 
                                            [](auto&& msg) { DEBUG(1, "    no result: ", msg) });
          if (check) {
            for (Clause* res : iterTraits(_rule.applyRule(lhs, VarBanks::internal, rhs, VarBanks::query, sigma))) {
              DEBUG(0, "    result: ", *res)
              out.push(res);
            }
            DEBUG(0, "")
          }
        }
      }
    }
    DEBUG(0, "")
    return pvi(arrayIter(std::move(out)));
  }

};


template<class Rule>
struct TriInf
: public GeneratingInferenceEngine
{
  using Premise0 = typename Rule::Premise0;
  using Premise1 = typename Rule::Premise1;
  using Premise2 = typename Rule::Premise2;
  static constexpr int bank(unsigned i) { return i * 2; }
  static constexpr int bankNorm(unsigned i) { return i * 2 + 1; }
  template<unsigned q, unsigned i>
  struct QueryBank {
    static constexpr int query = bank(q);
    static constexpr int internal = bank(i);
    static constexpr int normInternal = bankNorm(i);
  };
private:
  std::shared_ptr<AlascaState> _shared;
  Rule _rule;
  AlascaIndex<Premise0>* _prem0;
  AlascaIndex<Premise1>* _prem1;
  AlascaIndex<Premise2>* _prem2;
public:
  USE_ALLOCATOR(TriInf);

  TriInf(TriInf&&) = default;
  TriInf(std::shared_ptr<AlascaState> shared, Rule rule)
    : _shared(std::move(shared))
    , _rule(std::move(rule))
    , _prem0(nullptr)
    , _prem1(nullptr)
    , _prem2(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override
  { 
    ASS(!_prem0);
    ASS(!_prem1);
    ASS(!_prem2);

    GeneratingInferenceEngine::attach(salg);

    _prem0=static_cast<decltype(_prem0)> (_salg->getIndexManager()->request(Premise0::indexType()));
    _prem1=static_cast<decltype(_prem1)>(_salg->getIndexManager()->request(Premise1::indexType()));
    _prem2=static_cast<decltype(_prem2)>(_salg->getIndexManager()->request(Premise2::indexType()));

    _prem0->setShared(_shared);
    _prem1->setShared(_shared);
    _prem2->setShared(_shared);
  }

  void detach() final override {
    ASS(_salg);
    _prem0 = nullptr;
    _prem1 = nullptr;
    _prem2 = nullptr;
    _salg->getIndexManager()->release(Premise0::indexType());
    _salg->getIndexManager()->release(Premise1::indexType());
    _salg->getIndexManager()->release(Premise2::indexType());
    GeneratingInferenceEngine::detach();
  }

  template<unsigned p>
  auto getIdx() { return std::get<p>(std::tie(_prem0, _prem1, _prem2)); }

  // TODO make more generic (?)
  template<unsigned p>
  using Prem = TL::Get<p, TL::List<Premise0, Premise1, Premise2>>;

  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(__SelectedLiteral const& selection) override
  {
    auto unif_ = std::unique_ptr<AbstractingUnifier>(move_to_heap(AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF))));
    auto* unif = unif_.get();
#define LOOKAHEAD_ITER(i, j, k)                                                           \
      dropElementType(Prem<i>::iter(*_shared, selection)                                  \
        .flatMap([=](auto pi) {                                                           \
          ASS(unif->subs().isEmpty())                                                     \
          return getIdx<j>()->template find<QueryBank<i, j>>(unif, pi.key())              \
            .flatMap([=](auto pj)                                                         \
              { return getIdx<k>()->template find<QueryBank<i, k>>(unif, pi.key()); });   \
          }))                                                                             \

    // TODO set retrieveSubst false in find
    return pvi(concatIters(
       LOOKAHEAD_ITER(0, 1, 2),
       LOOKAHEAD_ITER(1, 0, 2),
       LOOKAHEAD_ITER(2, 0, 1)
    ).store(std::move(unif_)));
  }


  ClauseIterator generateClauses(Clause* premise) final override
  {
    ASS(_prem0)
    ASS(_prem1)
    ASS(_prem2)
    ASS(_shared)

    // TODO get rid of stack
    Stack<Clause*> out;
    auto sigma = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));

    for (auto const& prem0 : Premise0::iter(*_shared, premise)) {
      DEBUG(0, "prem0: ", prem0)
      for (auto prem1_sigma : _prem1->template find<QueryBank<0, 1>>(&sigma, prem0.key())) {
        auto& prem1   = *prem1_sigma.data;
        DEBUG(0, "  prem1: ", prem1)
        for (auto prem2_sigma : _prem2->template find<QueryBank<0, 2>>(&sigma, prem0.key())) {
          auto& prem2   = *prem2_sigma.data;
          DEBUG(0, "    prem2: ", prem2)
          for (Clause* res : iterTraits(_rule.applyRule(prem0, bank(0), 
                                                        prem1, bank(1), 
                                                        prem2, bank(2), sigma))) {
            DEBUG(0, "      result: ", *res)
            out.push(res);
          }
        }
        DEBUG(0, "")
      }
    }


    ASS(sigma.isEmpty())

    for (auto const& prem1 : Premise1::iter(*_shared, premise)) {
      DEBUG(0, "prem1: ", prem1)
      for (auto prem0_sigma : _prem0->template find<QueryBank<1, 0>>(&sigma, prem1.key())) {
        auto& prem0   = *prem0_sigma.data;
        if (prem0.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(0, "  prem0: ", prem0)
          for (auto prem2_sigma : _prem2->template find<QueryBank<0, 2>>(&sigma, prem0.key())) {
            auto& prem2   = *prem2_sigma.data;
            DEBUG(0, "    prem2: ", prem2)
            for (Clause* res : iterTraits(_rule.applyRule(prem0, bank(0), 
                                                          prem1, bank(1), 
                                                          prem2, bank(2), sigma))) {
              DEBUG(0, "      result: ", *res)
              out.push(res);
            }
            DEBUG(0, "")
          }
        }
      }
    }
    ASS(sigma.isEmpty())

    for (auto const& prem2 : Premise2::iter(*_shared, premise)) {
      DEBUG(0, "prem2: ", prem2)
      for (auto prem0_sigma : _prem0->template find<QueryBank<2, 0>>(&sigma, prem2.key())) {
        auto& prem0   = *prem0_sigma.data;
        // if (prem0.clause() != premise && prem2.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(0, "  prem0: ", prem0)
          for (auto prem1_sigma : _prem1->template find<QueryBank<0, 1>>(&sigma, prem0.key())) {
            auto& prem1   = *prem1_sigma.data;
            DEBUG(0, "    prem1: ", prem1)
            for (Clause* res : iterTraits(_rule.applyRule(prem0, bank(0), 
                                                          prem1, bank(1), 
                                                          prem2, bank(2), sigma))) {
              DEBUG(0, "      result: ", *res)
              out.push(res);
            }
            DEBUG(0, "")
          }
        // }
      }
    }

    return pvi(arrayIter(std::move(out)));
  }

};

/* rule of the shape
 *
 * Condition[key]       ToSimpl[key σ]
 * =======================================
 *           Concl[key σ]
 *
 * where ToSimpl is becoming redundant
 */
template<class Rule>
struct BinSimpl
: public BackwardSimplificationEngine
, public ForwardSimplificationEngine
{
  using ToSimpl = typename Rule::ToSimpl;
  using Condition = typename Rule::Condition;
  using Key = KeyType<ToSimpl>;
  static_assert(std::is_same_v<KeyType<ToSimpl>, KeyType<Condition>>);
private:
  virtual const char* name() const final override { return Rule::name(); } 
  std::shared_ptr<AlascaState> _shared;
  Rule _rule;
  static_assert(std::is_same_v<ToSimpl  , ELEMENT_TYPE(decltype(ToSimpl::iter(assertionViolation<AlascaState&>(), assertionViolation<Clause*>())))>);
  static_assert(std::is_same_v<Condition, ELEMENT_TYPE(decltype(Condition::iter(assertionViolation<AlascaState&>(), assertionViolation<Clause*>())))>);
  AlascaIndex<ToSimpl>* _toSimpl;
  AlascaIndex<Condition>* _condition;
  auto salg() const { return ForwardSimplificationEngine::_salg; }
public:
  USE_ALLOCATOR(BinSimpl);

  BinSimpl(BinSimpl&&) = default;

  template<class... Args>
  BinSimpl(std::shared_ptr<AlascaState> shared, Args... args)
    : BinSimpl(shared, Rule(shared, std::move(args)...))
  {  }

  BinSimpl(std::shared_ptr<AlascaState> shared, Rule rule)
    : _shared(std::move(shared))
    , _rule(std::move(rule))
    , _toSimpl(nullptr)
    , _condition(nullptr)
  {  }

  void attach(SaturationAlgorithm* s) final override
  { 
    ASS(!_condition);
    ASS(!_toSimpl);
    ForwardSimplificationEngine::attach(s);

    _toSimpl=static_cast<decltype(_toSimpl)>(salg()->getIndexManager()->request(  ToSimpl::indexType()));
    _condition=static_cast<decltype(_condition)>(salg()->getIndexManager()->request(Condition::indexType()));

    _toSimpl->setShared(_shared);
    _condition->setShared(_shared);

    attachToInner(_rule, s);
  }

  void detach() final override {
    ASS(salg());
    _toSimpl = nullptr;
    _condition = nullptr;
    salg()->getIndexManager()->release(ToSimpl::indexType());
    salg()->getIndexManager()->release(Condition::indexType());
    ForwardSimplificationEngine::detach();
  }


#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) final override
  {
    _toSimpl = (decltype(_toSimpl)) indices[0]; 
    _toSimpl->setShared(_shared);
    _condition = (decltype(_condition)) indices[1]; 
    _condition->setShared(_shared);
  }
  static auto testToSimplIdx() { return new AlascaIndex<ToSimpl>(); }
  static auto testConditionIdx() { return new AlascaIndex<Condition>(); }
#endif


  /* forward */ 
  virtual bool perform(Clause* toSimpl, Clause*& concl, ClauseIterator& conditions) final override {
    for (auto simpl : ToSimpl::iter(*_shared, toSimpl)) {
      for (auto sigma_cond : _condition->generalizations(simpl, /* retrieveSubstitution */ true)) {
        auto& sigma = sigma_cond.unifier;
        auto& cond = *sigma_cond.data;
        if (auto res = _rule.apply(cond, simpl, [&](auto t) { return sigma->applyToBoundResult(t); })) {
          concl = *res;
          conditions = pvi(getSingletonIterator(cond.clause()));
          return true;
        }
      }
    }
    return false;
  }

  /* backward */ 
  virtual void perform(Clause* condClause, BwSimplificationRecordIterator& simplifications) final override {

    /* in some simplification diamond rewrites can happen.
     * examples: clause p(f(a), f(b)) and f(x) = x
     *
     *   p(f(a), f(b)) -> p(a, f(b))
     *       |               |
     *       v               v
     *   p(f(a), b)    -> p(a, b)
     *
     * we can block this by simplifying every clause only once with f(x) = x
     */
    auto _alreadySimplified = std::make_unique<Set<Clause*>>();
    auto alreadySimplified = _alreadySimplified.get();

    auto result = Condition::iter(*_shared, condClause)
      .flatMap([this,alreadySimplified](auto cond) {
          return _toSimpl->instances(cond, /* retrieveSubstitution */ true)
            .filterMap([this,cond,alreadySimplified](auto sigma_simpl) -> Option<BwSimplificationRecord> {
                auto& sigma = sigma_simpl.unifier;
                auto& simpl = *sigma_simpl.data;

                if (alreadySimplified->contains(simpl.clause())) {
                  return {};
                }
                if (auto concl = _rule.apply(cond, simpl, [&](auto t) { return sigma->applyToBoundQuery(t); })) {
                  alreadySimplified->insert(simpl.clause());
                  return some(BwSimplificationRecord(simpl.clause(), *concl));
                } else {
                  return {};
                }

            });
      })
      .store(std::move(_alreadySimplified));
    
    /* TODO due to some mess (*) in saturation algorithm we have to convert everything to 
     * a stack and then into an iterator again. This should be resolved in staturation 
     * algorithm and a proper iterator should be returned here. and in other backward 
     * simplifications.
     * (*) the mess is that in saturation algorithm is that it removes from the passive index 
     * while we are still iterating, which is obviously not allowed as the backward simpl iterator 
     * must iterate over the passive set.
     */
    RStack<BwSimplificationRecord> resultStack;
    resultStack->loadFromIterator(std::move(result));
    simplifications =  pvi(arrayIter(std::move(resultStack)));
  }
};  


#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_BinInf__*/
