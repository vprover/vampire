/**
 * @file AIGInferenceEngine.hpp
 * Defines class AIGInferenceEngine.
 */

#ifndef __AIGInferenceEngine__
#define __AIGInferenceEngine__

#include "Forwards.hpp"

#include "Lib/DHMultiset.hpp"
#include "Lib/DHSet.hpp"

#include "AIG.hpp"


namespace Shell {

using namespace Lib;

class AIGInferenceEngine
{
public:
  virtual ~AIGInferenceEngine() {}

  void addValidNode(AIGRef node);
  void removeValidNode(AIGRef node);

  virtual AIGRef apply(AIGRef a, AIGStack* premises) = 0;

protected:
  //for these two functions it is ensured that a particular node
  //is not added the second time if it has not been removed before
  virtual void addValidNodeImpl(AIGRef node) {}
  virtual void removeValidNodeImpl(AIGRef node) {}

private:
  DHMultiset<AIGRef> _presentNodes;
};

class BottomUpAIGEngine : public AIGInferenceEngine
{
public:
  BottomUpAIGEngine(AIG& aig) : _aig(aig), _atr(aig) {}

  AIGRef apply(AIGRef a, AIGStack* premises);

protected:
  void addPremise(AIGRef prem);
  AIGRef level0Deref(AIGRef a);
  AIGRef level1Deref(AIGRef a);
  virtual AIGRef applyImpl(AIGRef a) = 0;

  AIG& _aig;
private:

  AIGInsideOutPosIterator _buildingIterator;

  DHSet<AIGRef> _currPremiseSet;
  AIGStack* _currPremises;

  AIGTransformer::RefMap _localCache;

  AIGTransformer _atr;
};

class AIGEquivUtils
{
public:
  /**
   * Represents normalized equivalence
   */
  struct Equiv {
    Equiv() {}
    Equiv(AIGRef first_, AIGRef second_);

    vstring toString() const { return "EQ: "+first.toString()+" <=> "+second.toString(); }

    AIGRef first;
    AIGRef second;
  };

  static bool isDisjEquiv(AIGRef a, Equiv& eq);

};

class AIGInliningEngine : public BottomUpAIGEngine
{
public:
  CLASS_NAME(AIGInliningEngine);
  USE_ALLOCATOR(AIGInliningEngine);
  
  AIGInliningEngine(AIG& aig) : BottomUpAIGEngine(aig) {}

protected:
  virtual void addValidNodeImpl(AIGRef node);
  virtual void removeValidNodeImpl(AIGRef node);

  virtual AIGRef applyImpl(AIGRef a);

private:
  void addRewrite(AIGRef src, AIGRef tgt, AIGRef premise);
  void orientEquivalence(AIGRef& lhs, AIGRef& rhs);

  struct RewriteRec {
    RewriteRec() {}
    RewriteRec(AIGRef tgt, AIGRef premise) : tgt(tgt), premise(premise) {}

    AIGRef tgt;
    AIGRef premise;
  };

  struct PremiseRec {
    AIGStack justifiedRewrites;
  };

  /**
   * Contains record of for which rewrites the key is a premise
   */
  DHMap<AIGRef,PremiseRec> _premRecs;
  DHMap<AIGRef,RewriteRec> _rewrites;
};

}

#endif // __AIGInferenceEngine__
