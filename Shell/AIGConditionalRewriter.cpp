/**
 * @file AIGConditionalRewriter.cpp
 * Implements class AIGConditionalRewriter.
 */

#include "AIGSubst.hpp"

#include "AIGConditionalRewriter.hpp"

namespace Shell
{

/////////////////////////
// AIGPrenexTransformer
//

bool AIGPrenexTransformer::containsQuant(AIGRef a0)
{
  CALL("AIGPrenexTransformer::containsQuant");

  static AIGInsideOutPosIterator ait;
  ait.reset(a0);
  while(ait.hasNext()) {
    AIGRef a = ait.next();
    if(a.isQuantifier()) {
      return false;
    }
  }
  return true;
}

bool AIGPrenexTransformer::isPrenex(AIGRef a)
{
  CALL("AIGPrenexTransformer::isPrenex");

  while(a.isQuantifier()) {
    a = a.parent(0);
  }
  return !containsQuant(a);
}

/**
 * Ensure that variables in segments of @c qs with the same quantifier
 * are sorted in ascending order.
 *
 * The implementation assumes that the segments usually are already sorted.
 */
void AIGPrenexTransformer::sortQuantSegments(QIStack& qs)
{
  CALL("AIGPrenexTransformer::sortQuantSegments");

  QuantInfo* qiArr = qs.begin();

  unsigned sz = qs.size();
  unsigned segStart = 0;
  bool segUnsorted = false;
  for(unsigned i=1; i<sz; i++) {
    if(qs[i-1].univ==qs[i].univ) {
      //we're staying in the same segment
      if(qs[i-1].var>qs[i].var) {
	segUnsorted = true;
      }
      continue;
    }
    if(segUnsorted) {
      std::sort(qiArr+segStart, qiArr+i, QuantInfo::compareVars);
    }
    segStart = i;
    segUnsorted = false;
  }
}

/**
 * Collect quantifiers from @c a which must be in prenex form.
 * Outer quantifiers go in the stack @c quants at the bottom.
 */
void AIGPrenexTransformer::collectQuants(AIGRef a, QIStack& quants, AIGRef& inner)
{
  CALL("AIGPrenexTransformer::collectQuants");
  ASS(quants.isEmpty());

  bool pol = true;
  while(a.isQuantifier()) {
    if(!a.polarity()) {
      pol = !pol;
    }
    AIG::VarSet::Iterator vit(*a.getQuantifierVars());
    while(vit.hasNext()) {
      unsigned var = vit.next();
      quants.push(QuantInfo(var, pol));
    }
    a = a.parent(0);
  }
  inner = a;

  //The requirement on QIStack is that variables in a block
  //of quantifiers of the same kind are sorted.
  //Even though the variables we get from VarSet::Iterator are in
  //ascending order, we still need to check sortedness to handle
  //the case with two nested quantifier nodes of the same kind.

  sortQuantSegments(quants);
}

void AIGPrenexTransformer::unifyQuants(AIGRef a1, const QIStack& q1, AIGRef a2, const QIStack& q2,
      AIGRef& a1res, AIGRef& a2res, QIStack& qres)
{
  CALL("AIGPrenexTransformer::unifyQuants");

  static DHMap<unsigned,unsigned> rnm1;
  static DHMap<unsigned,unsigned> rnm2;
  rnm1.reset();
  rnm2.reset();



  NOT_IMPLEMENTED;
}

AIGRef AIGPrenexTransformer::processConjunction(AIGRef a)
{
  CALL("AIGPrenexTransformer::processConjunction");
  ASS(a.isConjunction());
  ASS_EQ(a.parentCnt(),2);

  AIGRef p1 = a.parent(0);
  AIGRef p2 = a.parent(1);

  static QIStack p1Quants;
  static QIStack p2Quants;
  p1Quants.reset();
  p2Quants.reset();

  AIGRef inner1;
  AIGRef inner2;

  collectQuants(p1, p1Quants, inner1);
  collectQuants(p2, p2Quants, inner2);

  if(p1Quants.isEmpty() && p2Quants.isEmpty()) {
    return a;
  }

  static QIStack unifQuants;
  unifQuants.reset();



  NOT_IMPLEMENTED;
}

AIGRef AIGPrenexTransformer::apply(AIGRef a0)
{
  CALL("AIGPrenexTransformer::apply");

  _buildingIterator.addToTraversal(a0);

  while(_buildingIterator.hasNext()) {
    AIGRef src = _buildingIterator.next();
    AIGRef tgt;
    if(src.isAtom() || src.isPropConst()) {
      tgt = src;
    }
    else if(src.isQuantifier()) {
      tgt = _atr.lev1Deref(src, _transfCache);
    }
    else {
      ASS(src.isConjunction());
      tgt = processConjunction(src);
    }
    if(src!=tgt) {
      _transfCache.insert(src, tgt);
    }
  }

  AIGRef res = _atr.lev0Deref(a0, _transfCache);

  ASS(isPrenex(res));

  return res;
}




///////////////////////////
// AIGConditionalRewriter
//


}
