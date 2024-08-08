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

#define DEBUG(...) // DBG(__VA_ARGS__)

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

    for (auto const& lhs : Lhs::iter(*_shared, premise)) {
      DEBUG(1, "lhs: ", lhs)
      for (auto rhs_sigma : _rhs->find(lhs.key())) {
        auto& rhs   = *rhs_sigma.data;
        auto& sigma = rhs_sigma.unifier;
        DEBUG(1, "  rhs: ", rhs)
        auto res = _rule.applyRule(lhs, QUERY_BANK, rhs, RESULT_BANK, *sigma);
        for (Clause* res : iterTraits(_rule.applyRule(lhs, QUERY_BANK, rhs, RESULT_BANK, *sigma))) {
          DEBUG(1, "    result: ", *res)
          out.push(res);
        }
        DEBUG(1, "")
      }
    }

    for (auto const& rhs : Rhs::iter(*_shared, premise)) {
      DEBUG(1, "rhs: ", rhs)
      for (auto lhs_sigma : _lhs->find(rhs.key())) {
        auto& lhs   = *lhs_sigma.data;
        auto& sigma = lhs_sigma.unifier;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG(1, "  lhs: ", lhs)
          for (Clause* res : iterTraits(_rule.applyRule(lhs, RESULT_BANK, rhs, QUERY_BANK, *sigma))) {
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

#undef DEBUG
} // namespaceLASCA 
} // namespace Inferences

#endif /*__LASCA_BinInf__*/
