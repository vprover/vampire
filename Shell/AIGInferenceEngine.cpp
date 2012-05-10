/**
 * @file AIGInferenceEngine.cpp
 * Implements class AIGInferenceEngine.
 */

#include "AIGInferenceEngine.hpp"

namespace Shell
{

///////////////////////
// AIGInferenceEngine
//

void AIGInferenceEngine::addValidNode(AIGRef node)
{
  CALL("AIGInferenceEngine::addValidNodeImpl");

  int nodeMultiplicity = _presentNodes.insert(node);
  if(nodeMultiplicity==1) {
    //newly added node
    addValidNodeImpl(node);
  }
}

void AIGInferenceEngine::removeValidNode(AIGRef node)
{
  CALL("AIGInferenceEngine::removeValidNodeImpl");

  unsigned nodeOldMultiplicity = _presentNodes.getMultiplicityAndRemove(node);
  if(nodeOldMultiplicity==1) {
    //newly added node
    removeValidNodeImpl(node);
  }
}


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
    AIGRef curDer = level1Deref(cur);
    bool neg = !curDer.polarity();
    AIGRef curPosRes = applyImpl(curDer.getPositive());
    AIGRef curRes = neg ? curPosRes.neg() : curPosRes;
    if(cur!=curRes) {
      _localCache.insert(cur, curRes);
    }
    _buildingIterator.addToTraversal(curRes);
  }

  AIGRef res = level0Deref(a);
  return res;
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

///////////////////////
// AIGEquivUtils
//

AIGEquivUtils::Equiv::Equiv(AIGRef first_, AIGRef second_) : first(first_), second(second_)
{
  CALL("AIGConditionalRewriter::Equiv::Equiv");
  ASS_NEQ(first.getPositive(), second.getPositive());

  if(first.nodeIndex()>second.nodeIndex()) {
	swap(first,second);
  }

  if(!first.polarity()) {
    first = first.neg();
    second = second.neg();
  }
}


/**
 * Check for equivalence in the form
 * (a /\ b) \/ (~a /\ ~b)
 * in the term of AIGs written as ~and(~and(a,b),~and(~a,~b)).
 * They are called disjunction equivalences, as they have disjunction
 * at the top level.
 */
bool AIGEquivUtils::isDisjEquiv(AIGRef a, Equiv& eq)
{
  CALL("AIGEquivUtils::isDisjEquiv");

  if(!a.isConjunction() || a.polarity()) { return false; }

  AIGRef p1 = a.parent(0);
  AIGRef p2 = a.parent(1);
  if(p1.polarity() || p2.polarity() || !p1.isConjunction() || !p2.isConjunction()) { return false; }

  if( (p1.parent(0)==p2.parent(0).neg() && p1.parent(1)==p2.parent(1).neg()) ||
      (p1.parent(0)==p2.parent(1).neg() && p1.parent(1)==p2.parent(0).neg()) ) {
    eq.first = p1.parent(0);
    eq.second = p1.parent(1);

    if(!eq.first.polarity()) {
      eq.first = eq.first.neg();
      eq.second = eq.second.neg();
    }
    return true;
  }
  return false;
}


///////////////////////
// AIGInliningEngine
//

void AIGInliningEngine::orientEquivalence(AIGRef& lhs, AIGRef& rhs)
{
  CALL("AIGInliningEngine::orientEquivalence");

  if(lhs.isAtom()) {
  }
  else if(rhs.isAtom()) {
    //atom --> non-atom
    swap(rhs, lhs);
  }
}

void AIGInliningEngine::addValidNodeImpl(AIGRef node)
{
  CALL("AIGInliningEngine::addValidNodeImpl");
  ASS(!_premRecs.find(node));

  if(node.isPropConst()) { return; }

  if(node.polarity()) {
    addRewrite(node, _aig.getTrue(), node);
  }
  else {
    addRewrite(node.neg(), _aig.getFalse(), node);
  }

  AIGEquivUtils::Equiv eq;
  if(AIGEquivUtils::isDisjEquiv(node, eq)) {
    AIGRef lhs = eq.first;
    AIGRef rhs = eq.second;
    orientEquivalence(lhs, rhs);
    if(!lhs.polarity()) {
      lhs = lhs.neg();
      rhs = rhs.neg();
    }
    addRewrite(lhs, rhs, node);
  }
}

void AIGInliningEngine::removeValidNodeImpl(AIGRef node)
{
  CALL("AIGInliningEngine::removeValidNodeImpl");

  if(node.isPropConst()) { return; }

  if(!_premRecs.find(node)) {
    //nothing was justified by this node
    return;
  }

  const PremiseRec& premRec = _premRecs.get(node);
  AIGStack::ConstIterator jit(premRec.justifiedRewrites);
  while(jit.hasNext()) {
    AIGRef justified = jit.next();
    _rewrites.remove(justified);
  }
  _premRecs.remove(node);
}

/**
 * Rewrites are only from positive nodes
 */
void AIGInliningEngine::addRewrite(AIGRef src, AIGRef tgt, AIGRef premise)
{
  CALL("AIGInliningEngine::addRewrite");
  ASS(src.polarity());

  if(_rewrites.find(src)) {
    return;
  }

  PremiseRec* premRec;
  _premRecs.getValuePtr(premise, premRec, PremiseRec());

  premRec->justifiedRewrites.push(src);

  ALWAYS(_rewrites.insert(src, RewriteRec(tgt, premise)));
}


AIGRef AIGInliningEngine::applyImpl(AIGRef a)
{
  CALL("AIGInliningEngine::applyImpl");
  ASS(a.polarity());

  if(!_rewrites.find(a)) {
    return a;
  }

  const RewriteRec& rec = _rewrites.get(a);
  addPremise(rec.premise);
  return rec.tgt;
}

}
