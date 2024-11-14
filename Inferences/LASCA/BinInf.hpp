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

#ifndef __LASCA_BinInf__
#define __LASCA_BinInf__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Saturation/SaturationAlgorithm.hpp"
#include "Kernel/NumTraits.hpp"
#include "Kernel/Ordering.hpp"
#include "Indexing/LascaIndex.hpp"
#include "Shell/Options.hpp"
#include "Lib/TypeList.hpp"

#define DEBUG(lvl, ...)  if (lvl < 0) { DBG(__VA_ARGS__) }
namespace TL = Lib::TypeList;

namespace Inferences {
namespace LASCA {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class Rule>
struct BinInf
: public GeneratingInferenceEngine
{
  using Lhs = typename Rule::Lhs;
  using Rhs = typename Rule::Rhs;
  static constexpr int _lhsBank = 0;
  static constexpr int _rhsBank = 1;
  static constexpr int _internalBank = 2;
private:
  std::shared_ptr<LascaState> _shared;
  Rule _rule;
  LascaIndex<Lhs>* _lhs;
  LascaIndex<Rhs>* _rhs;
public:
  USE_ALLOCATOR(BinInf);

  BinInf(BinInf&&) = default;
  BinInf(std::shared_ptr<LascaState> shared, Rule rule)
    : _shared(std::move(shared))
    , _rule(std::move(rule))
    , _lhs(nullptr)
    , _rhs(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override
  { 
    ASS(!_rhs);
    ASS(!_lhs);

    GeneratingInferenceEngine::attach(salg);

    _lhs=static_cast<decltype(_lhs)> (_salg->getIndexManager()->request(Lhs::indexType()));
    _rhs=static_cast<decltype(_rhs)>(_salg->getIndexManager()->request(Rhs::indexType()));

    _lhs->setShared(_shared);
    _rhs->setShared(_shared);
  }

  void detach() final override {
    ASS(_salg);
    _lhs = nullptr;
    _rhs = nullptr;
    _salg->getIndexManager()->release(Lhs::indexType());
    _salg->getIndexManager()->release(Rhs::indexType());
    GeneratingInferenceEngine::detach();
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

  ClauseIterator generateClauses(Clause* premise) final override
  {
    ASS(_lhs)
    ASS(_rhs)
    ASS(_shared)

    // TODO get rid of stack
    Stack<Clause*> out;

    auto sigma = AbstractingUnifier::empty(AbstractionOracle(Shell::Options::UnificationWithAbstraction::OFF));
    ASS(sigma.isEmpty())

    for (auto const& lhs : Lhs::iter(*_shared, premise)) {
      DEBUG(1, "lhs: ", lhs)
      for (auto rhs_sigma : _rhs->find(&sigma, lhs.key(), _lhsBank, _internalBank, _rhsBank)) {
        auto& rhs   = *rhs_sigma.data;
        DEBUG(1, "  rhs: ", rhs)
        for (Clause* res : iterTraits(_rule.applyRule(lhs, _lhsBank, rhs, _rhsBank, sigma))) {
          DEBUG(1, "    result: ", *res)
          out.push(res);
        }
        DEBUG(1, "")
      }
    }

    ASS_REP(sigma.isEmpty(), sigma)

    for (auto const& rhs : Rhs::iter(*_shared, premise)) {
      DEBUG(1, "rhs: ", rhs)
      for (auto lhs_sigma : _lhs->find(&sigma, rhs.key(), _rhsBank, _internalBank, _lhsBank)) {
        auto& lhs   = *lhs_sigma.data;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(1, "  lhs: ", lhs)
          for (Clause* res : iterTraits(_rule.applyRule(lhs, _lhsBank, rhs, _rhsBank, sigma))) {
            DEBUG(1, "    result: ", *res)
            out.push(res);
          }
          DEBUG(1, "")
        }
      }
    }
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
  static constexpr int bankInternal(unsigned i) { return i * 2 + 1; }
private:
  std::shared_ptr<LascaState> _shared;
  Rule _rule;
  LascaIndex<Premise0>* _prem0;
  LascaIndex<Premise1>* _prem1;
  LascaIndex<Premise2>* _prem2;
public:
  USE_ALLOCATOR(TriInf);

  TriInf(TriInf&&) = default;
  TriInf(std::shared_ptr<LascaState> shared, Rule rule)
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
      DEBUG(1, "prem0: ", prem0)
      for (auto prem1_sigma : _prem1->find(&sigma, prem0.key(), bank(0), bankInternal(1), bank(1))) {
        auto& prem1   = *prem1_sigma.data;
        DEBUG(1, "  prem1: ", prem1)
        for (auto prem2_sigma : _prem2->find(&sigma, prem0.key(), bank(0), bankInternal(2), bank(2))) {
          auto& prem2   = *prem2_sigma.data;
          DEBUG(1, "    prem2: ", prem2)
          for (Clause* res : iterTraits(_rule.applyRule(prem0, bank(0), 
                                                        prem1, bank(1), 
                                                        prem2, bank(2), sigma))) {
            DEBUG(1, "      result: ", *res)
            out.push(res);
          }
        }
        DEBUG(1, "")
      }
    }


    ASS(sigma.isEmpty())

    for (auto const& prem1 : Premise1::iter(*_shared, premise)) {
      DEBUG(1, "prem1: ", prem1)
      for (auto prem0_sigma : _prem0->find(&sigma, prem1.key(), bank(1), bankInternal(0), bank(0))) {
        auto& prem0   = *prem0_sigma.data;
        if (prem0.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(1, "  prem0: ", prem0)
          for (auto prem2_sigma : _prem2->find(&sigma, prem0.key(), bank(0), bankInternal(2), bank(2))) {
            auto& prem2   = *prem2_sigma.data;
            DEBUG(1, "    prem2: ", prem2)
            for (Clause* res : iterTraits(_rule.applyRule(prem0, bank(0), 
                                                          prem1, bank(1), 
                                                          prem2, bank(2), sigma))) {
              DEBUG(1, "      result: ", *res)
              out.push(res);
            }
            DEBUG(1, "")
          }
        }
      }
    }
    ASS(sigma.isEmpty())

    for (auto const& prem2 : Premise2::iter(*_shared, premise)) {
      DEBUG(1, "prem2: ", prem2)
      for (auto prem0_sigma : _prem0->find(&sigma, prem2.key(), bank(2), bankInternal(0), bank(0))) {
        auto& prem0   = *prem0_sigma.data;
        // if (prem0.clause() != premise && prem2.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(1, "  prem0: ", prem0)
          for (auto prem1_sigma : _prem1->find(&sigma, prem0.key(), bank(0), bankInternal(1), bank(1))) {
            auto& prem1   = *prem1_sigma.data;
            DEBUG(1, "    prem1: ", prem1)
            for (Clause* res : iterTraits(_rule.applyRule(prem0, bank(0), 
                                                          prem1, bank(1), 
                                                          prem2, bank(2), sigma))) {
              DEBUG(1, "      result: ", *res)
              out.push(res);
            }
            DEBUG(1, "")
          }
        // }
      }
    }

    return pvi(arrayIter(std::move(out)));
  }

};

#undef DEBUG
} // namespaceLASCA 
} // namespace Inferences

#endif /*__LASCA_BinInf__*/
