/**
 * @file AIGInferenceEngine.hpp
 * Defines class AIGInferenceEngine.
 */

#ifndef __AIGInferenceEngine__
#define __AIGInferenceEngine__

#include "Forwards.hpp"

#include "Lib/DHSet.hpp"

#include "AIG.hpp"


namespace Shell {

using namespace Lib;

class AIGInferenceEngine
{
public:
  virtual ~AIGInferenceEngine() {}

  virtual void addValidNode(AIGRef node) {}
  virtual void removeValidNode(AIGRef node) {}

  virtual AIGRef apply(AIGRef a, AIGStack* premises) = 0;
};

class BottomUpAIGEngine : public AIGInferenceEngine
{
public:
  BottomUpAIGEngine(AIG& aig) : _aig(aig), _atr(aig) {}

  virtual AIGRef apply(AIGRef a, AIGStack* premises);

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

}

#endif // __AIGInferenceEngine__
