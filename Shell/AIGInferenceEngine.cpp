/**
 * @file AIGInferenceEngine.cpp
 * Implements class AIGInferenceEngine.
 */

#include "AIGInferenceEngine.hpp"

namespace Shell
{


///////////////////////
// BottomUpAIGEngine
//

/**
 * If we're not interested in premises, pass 0 as the @c premises value
 */
AIGRef BottomUpAIGEngine::apply(AIGRef a, AIGStack* premises)
{
  CALL("BottomUpAIGEngine::apply");

  _currPremiseSet.reset();
  _currPremises = premises;
  _localCache.reset();

  _buildingIterator.reset(a);
  while(_buildingIterator.hasNext()) {
    AIGRef cur = _buildingIterator.next();
  }

  NOT_IMPLEMENTED;
}

AIGRef BottomUpAIGEngine::level0Deref(AIGRef a)
{
  CALL("BottomUpAIGEngine::level0Deref");

  return _atr.lev0Deref(a, _localCache);
}

AIGRef BottomUpAIGEngine::level1Deref(AIGRef a)
{
  CALL("BottomUpAIGEngine::level1Deref");

  return _atr.lev1Deref(a, _localCache);
}

void BottomUpAIGEngine::addPremise(AIGRef prem)
{
  CALL("BottomUpAIGEngine::addPremise");
  if(_currPremises) {
    if(_currPremiseSet.insert(prem)) {
      _currPremises->push(prem);
    }
  }
}


}
