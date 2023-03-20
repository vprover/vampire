/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __BinaryInferenceEngine__
#define __BinaryInferenceEngine__

#include "Forwards.hpp"

#include "Inferences/InferenceEngine.hpp"
#include "Kernel/NumTraits.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Shell/Options.hpp"
#include "Indexing/IndexManager.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Inferences {


using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class BinInf>
class BinaryInferenceEngine
: public GeneratingInferenceEngine
{
#define DEBUG_BIN_INF(lvl, ...) if (lvl < BinInf::DEBUG_LEVEL) DBG(__VA_ARGS__)
public:
  CLASS_NAME(BinaryInferenceEngine);
  USE_ALLOCATOR(BinaryInferenceEngine);

  using Lhs = typename BinInf::Lhs;
  using Rhs = typename BinInf::Rhs;

  BinaryInferenceEngine(BinaryInferenceEngine&&) = default;
  BinaryInferenceEngine(BinInf inf) 
    : _inf(std::move(inf))
    , _lhs(nullptr)
    , _rhs(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override
  { 
    CALL("BinaryInferenceEngine::attach");
    ASS(!_rhs);
    ASS(!_lhs);
    GeneratingInferenceEngine::attach(salg);
    _lhs=static_cast<decltype(_lhs)> (salg->getIndexManager()->request(_inf.lhsIndexType()));
    _rhs=static_cast<decltype(_rhs)>(_salg->getIndexManager()->request(_inf.rhsIndexType()));
  }

  void detach() final override
  {
    CALL("BinaryInferenceEngine::detach");
    ASS(_salg);
    _salg->getIndexManager()->release(_inf.lhsIndexType());
    _salg->getIndexManager()->release(_inf.rhsIndexType());
    _lhs=0;
    _rhs=0;
    GeneratingInferenceEngine::detach();
  }


  ClauseIterator generateClauses(Clause* premise) final override
  {
    CALL("BinaryInferenceEngine::generateClauses(Clause* premise)")
    ASS(_lhs)
    ASS(_rhs)
    // TODO get rid of stack
    Stack<Clause*> out;

    for (auto const& lhs : iterTraits(_inf.iterLhs(premise))) {
      DEBUG_BIN_INF(1, "lhs: ", lhs)
      for (auto rhs_sigma : iterTraits(_rhs->getUnifications(lhs.key(), /* subs */ true))) {
        auto& rhs   = *rhs_sigma.data;
        auto& sigma = rhs_sigma.unifier;
        DEBUG_BIN_INF(1, "  rhs: ", rhs)
        auto res = _inf.apply(lhs, QUERY_BANK, rhs, RESULT_BANK, *sigma);
        DEBUG_BIN_INF(1, "")
        if (res != nullptr) {
          out.push(res);
        }
      }
    }

    for (auto const& rhs : iterTraits(_inf.iterRhs(premise))) {
      DEBUG(1, "rhs: ", rhs)
      for (auto lhs_sigma : iterTraits(_lhs->getUnifications(rhs.key(), /* subs */ true))) {
        auto& lhs   = *lhs_sigma.data;
        auto& sigma = lhs_sigma.unifier;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG_BIN_INF(1, "  lhs: ", lhs)
          auto res = _inf.apply(lhs, RESULT_BANK, rhs, QUERY_BANK, *sigma);
          DEBUG_BIN_INF(1, "")
          if (res != nullptr) {
            out.push(res);
          }
        }
      }
    }
    return pvi(arrayIter(std::move(out)));
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) final override
  {
    _lhs = (decltype(_lhs)) indices[0]; 
    _rhs = (decltype(_rhs)) indices[1]; 
  }
#endif

  BinInf _inf;
  LiteralIndex<Lhs>* _lhs;
  LiteralIndex<Rhs>* _rhs;
#undef DEBUG_BIN_INF
};

#undef DEBUG
} // namespace Inferences

#endif /*__BinaryInferenceEngine__*/
