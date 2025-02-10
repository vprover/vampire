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

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/ALASCA/Index.hpp"
#include "Lib/Metaiterators.hpp"
#include "Shell/Options.hpp"
#include "Lib/TypeList.hpp"

#define DEBUG(lvl, ...)  if (lvl < 0) { DBG(__VA_ARGS__) }
namespace TL = Lib::TypeList;

namespace Inferences {
namespace ALASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

 
template<class Inner>
void attachToInner(Inner& inner, SaturationAlgorithm* salg) { }
  
template<class Rule>
struct BinInf
: public NewGeneratingInference
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
    
  void attach(SaturationAlgorithm* salg) final override
  { 
    ASS(!_rhs);
    ASS(!_lhs);

    NewGeneratingInference::attach(salg);

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
    NewGeneratingInference::detach();
  }


#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) final override
  {
    _lhs = (decltype(_lhs)) indices[0]; 
    _lhs->setShared(_shared);
    _rhs = (decltype(_rhs)) indices[1]; 
    _rhs->setShared(_shared);
  }
#endif

private:
  template<class Iter>
  [[deprecated("return a proper Result instead from applyRule")]]
  static Option<Result> toResult(Iter iter, Lhs const& lhs, Rhs const& rhs) {
    return some(Result { 
      .hypotheses = pvi(iterItems(lhs.clause(), rhs.clause())),
      .generated = pvi(std::move(iter)),
      .redundant = VirtualIterator<Clause*>::getEmpty(),
    });
  }

  static Option<Result> toResult(Option<Result> res, Lhs const& lhs, Rhs const& rhs)
  { return res; }

public:
  VirtualIterator<Result> apply(Clause* premise) final override
  {
    ASS(_lhs)
    ASS(_rhs)
    ASS(_shared)

    // TODO get rid of stack
    Stack<Result> out;

    auto sigma = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
    ASS(sigma.isEmpty())

    using VarBanks  = Indexing::RetrievalAlgorithms::DefaultVarBanks;
    auto applyRuleAndLog = [&](auto& lhs, auto& lbank, auto& rhs, auto& rbank) {
      RStack<Clause*> rs;
      if (auto result = toResult(_rule.applyRule(lhs, lbank, rhs, rbank, sigma), lhs, rhs)) {
        rs->loadFromIterator(result->generated);
        if (rs.size() > 0) {
          for (auto cl : *rs) {
            DEBUG(0, "    result: ", *cl)
          }
          DEBUG(0, "")
        } else {
          DEBUG(0, "<nothing>")
        }
        result->generated = pvi(arrayIter(std::move(rs)));
        out.push(std::move(*result));
      }
    };

    DEBUG(0, _rule.name())
    for (auto const& lhs : Lhs::iter(*_shared, premise)) {
      DEBUG(0, "lhs: ", lhs, " (", lhs.clause()->number(), ")")
      for (auto rhs_sigma : _rhs->template find<VarBanks>(&sigma, lhs.key())) {
        auto& rhs   = *rhs_sigma.data;
        DEBUG(0, "  rhs: ", rhs, " (", rhs.clause()->number(), ")")
        DEBUG(0, "  sigma: ", sigma)

        applyRuleAndLog(lhs, VarBanks::query, rhs, VarBanks::internal);
      }
    }

    ASS_REP(sigma.isEmpty(), sigma)

    for (auto const& rhs : Rhs::iter(*_shared, premise)) {
      DEBUG(0, "rhs: ", rhs, " (", rhs.clause()->number(), ")")
      for (auto lhs_sigma : _lhs->template find<VarBanks>(&sigma, rhs.key())) {
        auto& lhs   = *lhs_sigma.data;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          applyRuleAndLog(lhs, VarBanks::internal, rhs, VarBanks::query);
        }
      }
    }
    DEBUG(0, "")
    return pvi(arrayIter(std::move(out)));
  }

};

template<class Rule>
struct TriInf
: public NewGeneratingInference
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

    NewGeneratingInference::attach(salg);

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
    NewGeneratingInference::detach();
  }


#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) final override
  {
    _prem0 = (decltype(_prem0)) indices[0]; 
    _prem1 = (decltype(_prem1)) indices[1]; 
    _prem2 = (decltype(_prem2)) indices[2]; 
    _prem0->setShared(_shared);
    _prem1->setShared(_shared);
    _prem2->setShared(_shared);
  }
#endif

  template<unsigned p>
  auto getIdx() { return std::get<p>(std::tie(_prem0, _prem1, _prem2)); }

  // TODO make more generic (?)
  template<unsigned p>
  using Prem = TL::Get<p, TL::List<Premise0, Premise1, Premise2>>;

  

  VirtualIterator<Result> apply(Clause* premise) final override
  {
    ASS(_prem0)
    ASS(_prem1)
    ASS(_prem2)
    ASS(_shared)

    // TODO get rid of stack
    Stack<Result> out;
    auto sigma = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));

    auto applyRuleAndLog = [&](auto& prem0, auto& prem1, auto& prem2) {
      RStack<Clause*> rs;
      rs->loadFromIterator(_rule.applyRule(prem0, bank(0), 
                                           prem1, bank(1), 
                                           prem2, bank(2), sigma));
      if (rs.size() > 0) {
        for (auto cl : *rs) {
          DEBUG(0, "    result: ", *cl)
        }
        DEBUG(0, "")
      } else {
        DEBUG(0, "<nothing>")
      }
      out.push(Result { 
          .hypotheses = pvi(iterItems(prem0.clause(), prem1.clause(), prem2.clause())),
          .generated = pvi(arrayIter(std::move(rs))),
          .redundant = VirtualIterator<Clause*>::getEmpty(),
          });
    };

    for (auto const& prem0 : Premise0::iter(*_shared, premise)) {
      DEBUG(0, "prem0: ", prem0)
      for (auto prem1_sigma : _prem1->template find<QueryBank<0, 1>>(&sigma, prem0.key())) {
        auto& prem1   = *prem1_sigma.data;
        DEBUG(0, "  prem1: ", prem1)
        for (auto prem2_sigma : _prem2->template find<QueryBank<0, 2>>(&sigma, prem0.key())) {
          auto& prem2   = *prem2_sigma.data;
          DEBUG(0, "    prem2: ", prem2)
          applyRuleAndLog(prem0, prem1, prem2);
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
            applyRuleAndLog(prem0, prem1, prem2);
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
            applyRuleAndLog(prem0, prem1, prem2);
          }
        // }
      }
    }

    return pvi(arrayIter(std::move(out)));
  }

};

#undef DEBUG
} // namespaceALASCA 
} // namespace Inferences

#endif /*__ALASCA_Inferences_BinInf__*/
