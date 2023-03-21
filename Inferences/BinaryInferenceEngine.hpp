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

#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Inferences/InferenceEngine.hpp"
#include "Kernel/NumTraits.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Shell/Options.hpp"
#include "Indexing/IndexManager.hpp"
#include "Indexing/LiteralIndex.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {


using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

template<class Key, class Data> 
struct AutoSubstTreeInner;

template<class Data> 
struct AutoSubstTreeInner<Literal*, Data> 
{ using type = LiteralSubstitutionTree<Data>; };

template<class Data> 
struct AutoSubstTreeInner<TypedTermList, Data> 
{ using type = TermSubstitutionTree<Data>; };

template<class Data>
class AutoSubstitutionTree
: public Index
{
  using Key = typename Data::Key;
  typename AutoSubstTreeInner<Key, Data>::type _self;
public:
  CLASS_NAME(AutoSubstitutionTree);
  USE_ALLOCATOR(AutoSubstitutionTree);

  AutoSubstitutionTree() : _self() {}

  auto handle(Data data, bool adding) 
  { _self.handle(std::move(data), adding); }

  auto unifications(Key const& key)
  { return _self.unifications(key); }

  friend std::ostream& operator<<(std::ostream& out, AutoSubstitutionTree const& self)
  { return *self._self; }
};

#define DEBUG_BIN_INF(lvl, ...) if (lvl < BinInf::DEBUG_LEVEL) DBG(__VA_ARGS__)

template<class BinInf>
class BinInfIndex
: public Index
{
  using Lhs = typename BinInf::Lhs;
  using Rhs = typename BinInf::Rhs;
  AutoSubstitutionTree<Lhs> _lhs;
  AutoSubstitutionTree<Rhs> _rhs;
public:
  CLASS_NAME(BinInfIndex);
  USE_ALLOCATOR(BinInfIndex);

  BinInfIndex() : _lhs(), _rhs() {}

  auto findRhs(Lhs const& lhs) { return _rhs.unifications(lhs.key()); }
  auto findLhs(Rhs const& rhs) { return _lhs.unifications(rhs.key()); }


  void handleClause(Clause* c, bool adding) override 
  {
    for (auto x : iterTraits(Lhs::iter(c))) {
      DEBUG_BIN_INF(1, "inserting lhs: ", x)
      _lhs.handle(std::move(x), adding);
    }
    for (auto x : iterTraits(Rhs::iter(c))) {
      DEBUG_BIN_INF(1, "inserting rhs: ", x)
      _rhs.handle(std::move(x), adding);
    }
  }

  friend std::ostream& operator<<(std::ostream& out, BinInfIndex const& self)
  { return *self._self; }
};


template<class BinInf>
class BinaryInferenceEngine
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(BinaryInferenceEngine);
  USE_ALLOCATOR(BinaryInferenceEngine);

  using Lhs = typename BinInf::Lhs;
  using Rhs = typename BinInf::Rhs;

  BinaryInferenceEngine(BinaryInferenceEngine&&) = default;
  BinaryInferenceEngine(BinInf inf) 
    : _inf(std::move(inf))
    , _idx(nullptr)
  {  }

  void attach(SaturationAlgorithm* salg) final override
  { 
    CALL("BinaryInferenceEngine::attach");
    ASS(!_idx);
    GeneratingInferenceEngine::attach(salg);
    _idx = static_cast<decltype(_idx)> (salg->getIndexManager()->request(_inf.indexType()));
  }

  void detach() final override
  {
    CALL("BinaryInferenceEngine::detach");
    ASS(_salg);
    _salg->getIndexManager()->release(_inf.indexType());
    _idx = 0;
    GeneratingInferenceEngine::detach();
  }


  ClauseIterator generateClauses(Clause* premise) final override
  {
    CALL("BinaryInferenceEngine::generateClauses(Clause* premise)")
    ASS(_idx)
    // TODO get rid of stack
    Stack<Clause*> out;

    // auto result = RESULT_BANK;
    // auto query  = QUERY_BANK;
    auto result = true;
    auto query  = false;
    for (auto const& lhs : iterTraits(_inf.iterLhs(premise))) {
      DEBUG_BIN_INF(0, "lhs: ", lhs)
      for (auto rhs_sigma : iterTraits(_idx->findRhs(lhs))) {
        auto& rhs   = *rhs_sigma.data;
        auto& sigma = rhs_sigma.unifier;
        DEBUG_BIN_INF(0, "  rhs: ", rhs)
        auto concl = _inf.apply(lhs, query, rhs, result, *sigma);
        DEBUG_BIN_INF(0, "")
        if (concl != nullptr) {
          out.push(concl);
        }
      }
    }

    for (auto const& rhs : iterTraits(_inf.iterRhs(premise))) {
      DEBUG_BIN_INF(0, "rhs: ", rhs)
      for (auto lhs_sigma : iterTraits(_idx->findLhs(rhs))) {
        auto& lhs   = *lhs_sigma.data;
        auto& sigma = lhs_sigma.unifier;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          DEBUG_BIN_INF(0, "  lhs: ", lhs)
          auto concl = _inf.apply(lhs, result, rhs, query, *sigma);
          DEBUG_BIN_INF(0, "")
          if (concl != nullptr) {
            out.push(concl);
          }
        }
      }
    }
    return pvi(arrayIter(std::move(out)));
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& indices) final override
  { _idx = (decltype(_idx)) indices[0]; }
#endif

  BinInf _inf;
  BinInfIndex<BinInf>* _idx;
#undef DEBUG_BIN_INF
};


#undef DEBUG
} // namespace Inferences

#endif /*__BinaryInferenceEngine__*/
