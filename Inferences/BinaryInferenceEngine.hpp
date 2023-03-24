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

#include "Debug/Assertion.hpp"
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
#include <memory>

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

  auto handle(Data data, bool adding) { _self.handle(std::move(data), adding); }
  auto getInstances(Key const& key) { return _self.getInstances(key); }
  auto getGeneralizations(Key const& key) { return _self.getGeneralizations(key); }
  auto getUnifications(Key const& key) { return _self.getUnifications(key); }

  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<AutoSubstitutionTree> const& self) { return out << multiline(self.self, self.indent); }
  friend std::ostream& operator<<(std::ostream& out, AutoSubstitutionTree const& self) { return out << self._self; }
};

#define DEBUG_BIN_INF(lvl, ...) if (lvl < BinInf::DEBUG_LEVEL) DBG(__VA_ARGS__)


namespace BinInfMatching {
  template<class Lhs, class Rhs>
  struct RightInstanceOfLeft 
  {
    static auto findRhs(AutoSubstitutionTree<Rhs>& rhs, Lhs const& lhs) { return rhs.getInstances(lhs.key()); }
    static auto findLhs(AutoSubstitutionTree<Lhs>& lhs, Rhs const& rhs) { return lhs.getGeneralizations(rhs.key()); }
  };

  template<class Lhs, class Rhs>
  struct Unification 
  {
    static auto findRhs(AutoSubstitutionTree<Rhs>& rhs, Lhs const& lhs) { return rhs.getUnifications(lhs.key()); }
    static auto findLhs(AutoSubstitutionTree<Lhs>& lhs, Rhs const& rhs) { return lhs.getUnifications(rhs.key()); }
  };
}


template<class BinInf>
class BinInfIndex
: public Index
{
  using Lhs = typename BinInf::Lhs;
  using Rhs = typename BinInf::Rhs;
  BinInf* _inf;
  AutoSubstitutionTree<Lhs> _lhs;
  AutoSubstitutionTree<Rhs> _rhs;
public:
  CLASS_NAME(BinInfIndex);
  USE_ALLOCATOR(BinInfIndex);

  BinInfIndex() : _inf(nullptr), _lhs(), _rhs() {}

  auto findRhs(Lhs const& lhs) { return BinInf::Matching::findRhs(_rhs, lhs); }
  auto findLhs(Rhs const& rhs) { return BinInf::Matching::findLhs(_lhs, rhs); }

  void handleClause(Clause* c, bool adding) override 
  {
    for (auto x : iterTraits(_inf->iterLhs(c))) {
      DEBUG_BIN_INF(1, "inserting lhs: ", x)
      _lhs.handle(std::move(x), adding);
    }
    for (auto x : iterTraits(_inf->iterRhs(c))) {
      DEBUG_BIN_INF(1, "inserting rhs: ", x)
      _rhs.handle(std::move(x), adding);
    }
  }

  void setInf(BinInf* inf) { _inf = inf; }

  friend std::ostream& operator<<(std::ostream& out, OutputMultiline<BinInfIndex> const& self) { return out << multiline(self.self, self.indent); }
  friend std::ostream& operator<<(std::ostream& out, BinInfIndex const& self) { return out << self._self; }
};

class RuleApplicationResultOk
{
  Recycled<Stack<Clause*>> _derived;
  Recycled<Stack<Clause*>> _redundant;
public:
  RuleApplicationResultOk() {}

  template<class... Args>
  RuleApplicationResultOk derived(Clause* cl1, Clause* cl2, Args... args) &&
  { 
    ASS(cl1)
    _derived->push(cl1); 
    return std::move(*this).derived(cl2, args...); 
  }

  RuleApplicationResultOk derived(Clause* cl) &&
  { 
    ASS(cl)
    _derived->push(cl); 
    return std::move(*this); 
  }


  template<class... Args>
  RuleApplicationResultOk redundant(Clause* cl1, Clause* cl2, Args... args) &&
  { 
    ASS(cl1)
    _redundant->push(cl1); 
    return std::move(*this).redundant(cl2, args...); 
  }

  RuleApplicationResultOk redundant(Clause* cl) &&
  { 
    ASS(cl)
    _redundant->push(cl); 
    return std::move(*this); 
  }

  Stack<Clause*> const& derived() const& { return *_derived; }
  Stack<Clause*> const& redundant() const& { return *_redundant; }

}; 

class RuleApplicationResultFail
{
public:
  template<class BinInf, class... Msg>
  RuleApplicationResultFail(BinInf& inf, Msg const&... msg)
  { DEBUG_BIN_INF(1, "application failed: ", msg...); }
}; 

class RuleApplicationResult 
: public Coproduct< RuleApplicationResultOk
                  , RuleApplicationResultFail> 
{
public:
  using Ok   = RuleApplicationResultOk;
  using Fail = RuleApplicationResultFail;

  RuleApplicationResult(Ok   ok)    : Coproduct(std::move(ok)) {}
  RuleApplicationResult(Fail fail)  : Coproduct(std::move(fail)) {}
  RuleApplicationResult(Clause* cl) : Coproduct(derived(cl)) {}


  template<class... Cs>
  static Ok derived(Cs... clauses)
  { return Ok().derived(std::move(clauses)...); }

  template<class BinInf, class... Msgs>
  static Fail fail(BinInf& inf, Msgs const&... msgs)
  { return Fail(inf, msgs...); }
};


template<class BinInf>
class BinaryInferenceEngine
: public SimplifyingGeneratingInference
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
  
  static_assert(std::is_same<typename Lhs::Key, typename Rhs::Key>::value, "keys of inference must be of the same type");

  void attach(SaturationAlgorithm* salg) final override
  { 
    CALL("BinaryInferenceEngine::attach");
    ASS(!_idx);
    SimplifyingGeneratingInference::attach(salg);
    _idx = static_cast<decltype(_idx)> (salg->getIndexManager()->request(_inf.indexType()));
    _idx->setInf(&_inf);
  }

  void detach() final override
  {
    CALL("BinaryInferenceEngine::detach");
    ASS(_salg);
    _idx->setInf(nullptr);
    _salg->getIndexManager()->release(_inf.indexType());
    _idx = 0;
    SimplifyingGeneratingInference::detach();
  }


  ClauseGenerationResult generateSimplify(Clause* premise) final override
  {
    CALL("BinaryInferenceEngine::generateClauses(Clause* premise)")
    ASS(_idx)
    Recycled<Stack<Clause*>> out;

    bool redundant = false;

    // auto result = RESULT_BANK;
    // auto query  = QUERY_BANK;
    auto result = true;
    auto query  = false;

    auto apply = [&](auto& lhs, auto lquery, auto& rhs, auto rquery, auto& sigma) {
      return _inf.apply(lhs, lquery, rhs, rquery, sigma)
            .match([&](RuleApplicationResult::Ok ok) {
                  for (auto c : ok.derived()) {
                    DEBUG_BIN_INF(0, "    derived: ", *c);
                    out->push(c);
                  }
                  for (auto c : ok.redundant()) {
                    if (c == premise) {
                      redundant = true;
                    } else {
                      ASSERTION_VIOLATION_REP("TODO")
                    }
                  }
                  ASS_REP(ok.redundant().size() == 0, "TODO")
                },
                [](RuleApplicationResult::Fail) { /* nothing to do */ });
    };

    for (auto const& lhs : iterTraits(_inf.iterLhs(premise))) {
      DEBUG_BIN_INF(0, "lhs: ", lhs)
      for (auto rhs_sigma : iterTraits(_idx->findRhs(lhs))) {
        auto& rhs   = *rhs_sigma.data;
        auto& sigma = rhs_sigma.unifier;
        DEBUG_BIN_INF(0, "  rhs: ", rhs)
        apply(lhs, query, rhs, result, *sigma);
      }
    }

    for (auto const& rhs : iterTraits(_inf.iterRhs(premise))) {
      DEBUG_BIN_INF(0, "rhs: ", rhs)
      for (auto lhs_sigma : iterTraits(_idx->findLhs(rhs))) {
        auto& lhs   = *lhs_sigma.data;
        auto& sigma = lhs_sigma.unifier;
        if (lhs.clause() != premise) { // <- self application. the same one has been run already in the previous loop
          apply(lhs, result, rhs, query, *sigma);
        }
      }
    }

    return ClauseGenerationResult {
      .clauses = pvi(arrayIter(std::move(out))),
      .premiseRedundant = redundant,
    };
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
