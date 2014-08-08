/**
 * @file BoundsArray.cpp
 * Implements class BoundsArray.
 */
#if GNUMP
#include <sstream>

#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"
#include "Kernel/Constraint.hpp"

#include "Solver.hpp"
#include "BoundsArray.hpp"

#undef LOGGING
#define LOGGING 0

namespace Solving
{

BoundJustification::BoundJustification(const BoundJustification& j)
 : _parent(j.parent()), _propagatedBounds(j.propagatedBounds().size())
{
  CALL("BoundJustification::BoundJustification(const BoundJustification&)");

  const BoundSpecArray& origPB = j.propagatedBounds();
  _propagatedBounds.initFromArray(origPB.size(), origPB.array());
}

BoundJustification& BoundJustification::operator=(const BoundJustification& j)
{
  CALL("BoundJustification::operator=");

  _parent = j.parent();
  const BoundSpecArray& origPB = j.propagatedBounds();
  _propagatedBounds.initFromArray(origPB.size(), origPB.array());
  return *this;
}

vstring BoundJustification::toString(const BoundsArray& bounds) const
{
  CALL("BoundJustification::toString");

  if(!parent()) {
    ASS_EQ(propagatedBounds().size(),0);
    return "{decision bound}";
  }
  vstring res = parent()->toString();

  BoundSpecArray::ConstIterator bsIt(_propagatedBounds);
  while(bsIt.hasNext()) {
    BoundSpec spec = bsIt.next();
    const BoundStack& bs = bounds.getBounds(spec.bound);
    const BoundInfo& bi = bs[spec.boundIndex];
    res += " & (" + bi.toString(bounds, spec.bound, false) + ")";
  }
  return res;
}

/**
 * Return string representation of the bound, assuming the bound is on variable
 * @c v and that it is left iff @c isLeftBound is true. If @c outputJustification
 * is true, include representation of the justification into the output.
 */
vstring BoundInfo::toString(const BoundsArray& bounds, const BoundId& b, bool outputJustification) const
{
  CALL("BoundInfo::toString");

  vstringstream stm;
  //stm << "[var:" << v << "] ";
  stm << (b.left ? " " : "-");
  stm << env.signature->varName(b.var);
  stm << (strict() ? ">" : ">=");
  stm << (b.left ? value() : -value());
  if(outputJustification) {
    stm << " <-- " << justification().toString(bounds);
  }
  return stm.str();
}


/**
 * Create a @c BoundsArray object for solver @c s.
 */
BoundsArray::BoundsArray(Solver& s)
: _parent(s), _left(s.varCnt()), _right(s.varCnt()) {}

const BoundInfo* BoundsArray::getBound(const BoundId& b) const
{
  CALL("BoundsArray::getBound");

  const BoundStack& bs = getBounds(b);
  if(bs.isEmpty()) {
    return 0;
  }
  return &bs.top();
}

bool BoundsArray::getBound(const BoundId& b, BoundNumber& val, bool& strict) const
{
  CALL("BoundsArray::getBound");

  const BoundInfo* bi = getBound(b);
  if(!bi) {
    return false;
  }
  val = bi->value();
  strict = bi->strict();
  return true;
}

bool BoundsArray::isUnbounded(const BoundId& b) const
{
  CALL("BoundsArray::isUnbounded");

  return getBounds(b).isEmpty();
}

/**
 * Return true if the tightest left or right bound (depending on
 * @c leftBound) of variable @b v comes from the current decision level.
 */
bool BoundsArray::isBoundedOnCurrentLevel(const BoundId& b) const
{
  CALL("BoundsArray::isBoundOnCurrentLevel");

  const BoundStack& bs = getBounds(b);
  return bs.isNonEmpty() && bs.top().depth()==getDepth();
}

/**
 * Return true if constraint @c c was used to infer some (either left or right,
 * depending on @c leftBound) bound of variable @b v on the current decision level.
 */
size_t BoundsArray::countBoundsByConstraintOnCurrentLevel(const BoundId& b, const Constraint& c) const
{
  CALL("BoundsArray::countBoundsByConstraintOnCurrentLevel");

  size_t res = 0;
  DecisionLevel depth = getDepth();
  const BoundStack& bs = getBounds(b);
  BoundStack::TopFirstIterator sit(const_cast<BoundStack&>(bs));
  while(sit.hasNext()) {
    const BoundInfo& bi = sit.next();
    ASS_LE(bi.depth(), depth);
    if(bi.depth()<depth) {
      return res;
    }
    if(bi.justification().parent()==&c) {
      res++;
    }
  }
  return res;
}

/**
 * Return true if a collapsing constraint was used to infer some (either left or right,
 * depending on @c leftBound) bound of variable @b v on the current decision level.
 */
bool BoundsArray::isBoundedByCollapsingConstraintOnCurrentLevel(const BoundId& b) const
{
  CALL("BoundsArray::isBoundedByCollapsingConstraintOnCurrentLevel");

  DecisionLevel depth = getDepth();
  const BoundStack& bs = getBounds(b);
  BoundStack::TopFirstIterator sit(const_cast<BoundStack&>(bs));
  while(sit.hasNext()) {
    const BoundInfo& bi = sit.next();
    ASS_LE(bi.depth(), depth);
    if(bi.depth()<depth) {
      return false;
    }
    if(bi.justification().parent()->collapsing()) {
      return true;
    }
  }
  return false;
}

/**
 * Return true if the left and right bound on variable @c v do
 * not overlap
 */
bool BoundsArray::hasConflict(Var v) const
{
  CALL("BoundsArray::hasConflict");

  const BoundInfo* left = getBound(BoundId(v, true));
  if(!left) { return false; }
  const BoundInfo* right = getBound(BoundId(v, false));
  if(!right) { return false; }

  return left->hasConflictWith(*right, true);
}

/**
 * Return true if the intersection of the left and right bound on the
 * value @c v is a single point
 */
bool BoundsArray::hasTightBound(Var v) const
{
  CALL("BoundsArray::hasTightBound");

  static BoundNumber leftVal, rightVal;
  bool leftStrict, rightStrict;

  if(!getBound(BoundId(v, true), leftVal, leftStrict) || !getBound(BoundId(v, false), rightVal, rightStrict)) {
    return false;
  }
  return leftVal==rightVal && !leftStrict && !rightStrict;
}

/**
 * Assuming the bound on the variable @c v is tight, return the
 * value of the single point intersection of the left and right bound.
 *
 * @see hasTightBound()
 */
BoundNumber BoundsArray::getTightBound(Var v) const
{
  CALL("BoundsArray::getTightBound");
  ASS(hasTightBound(v));

  static BoundNumber val;
  ALWAYS( getBound(BoundId(v, true), val) );
  return val;
}



void BoundsArray::makeDecisionAssignment(Var v, BoundNumber value)
{
  CALL("BoundsArray::makeDecisionAssignment");

  BoundId leftBoundId(v, true);
  BoundId rightBoundId(v, false);

  BoundInfo bound(value, false);

  //Perform assignment by adding left and right bound.
  //Assignment should never cause a conflict.
  ALWAYS( suggestBound(leftBoundId, bound, true)!=BS_CONFLICT );
  ALWAYS( suggestBound(rightBoundId, bound, true)!=BS_CONFLICT );
}

/**
 * If @c b is more precise than the either left or right bound
 * (as specified by @c leftBound), add it to the bounds array and
 * return either BS_IMPROVEMENT or BS_CONFLICT (in case the bound
 * caused a conflict). Otherwise return BS_NONE.
 *
 * Call to this function may modify the update queue and the conflict set.
 */
BoundSuggestionResult BoundsArray::suggestBound(const BoundId& b, const BoundInfo & inf, bool decisionPoint)
{
  CALL("BoundsArray::suggestBound");

  BoundStack& stack = getBounds(b);
  if(!decisionPoint && stack.isNonEmpty() && !stack.top().lessPreciseThan(inf, b.left)) {
    return BS_NONE;
  }

  //when we make a decision point, it still cannot be out of the previous bounds
  ASS(!stack.isNonEmpty() || stack.top().lessPreciseThan(inf, b.left) || (stack.top().value()==inf.value() &&  !stack.top().strict()));

  //if(stack.isNonEmpty()) { LOG ("diff " << (stack.top().value()-b.value()).abs()); }

  stack.push(inf);
  //assign the current depth to the bound
  stack.top().assignDepth(getDepth());

  _updateQueue.push_back(UpdateInfo(b, stack.size()-1));

  if(hasConflict(b.var)) {
    _conflictSet.insert(b.var);
    return BS_CONFLICT;
  }

  return BS_IMPROVEMENT;
}

DecisionLevel BoundsArray::getDepth() const
{
  CALL("BoundsArray::getDepth");
  return _parent.getDepth();
}

/**
 * @c boundIndex is the index of the bound on the BoundStack.
 * If equal to @c LATEST_BOUND_INDEX, the top of the stack
 * (i.e. the current bound) is considered.
 */
void BoundsArray::tryGetCollapsingInequality(const BoundId& b, size_t boundIndex,
    ConstraintRCPtr& result) const
{
  CALL("BoundsArray::getCollapsingInequality");

  const BoundStack& stack = getBounds(b);
  const BoundInfo& bi = (boundIndex==LATEST_BOUND_INDEX) ? stack.top() : stack[boundIndex];
  const BoundJustification& justification = bi.justification();
  if(!justification.parent()) {
    //bound does not come from bound propagation, so there is no collapsing inequality
    result = 0;
    return;
  }
  result = bi.tryGetCachedCollapsingInequality();
  if(result) {
    return;
  }

  ConstraintRCPtr c(justification.parent());
  BoundJustification::BoundSpecArray::ConstIterator pbIt(justification.propagatedBounds());
  while(pbIt.hasNext()) {
    BoundJustification::BoundSpec bs = pbIt.next();
    ConstraintRCPtr premiseCollapsingInequality;
    tryGetCollapsingInequality(bs.bound, bs.boundIndex, premiseCollapsingInequality);
    if(!premiseCollapsingInequality) {
      continue;
    }
    if(premiseCollapsingInequality->coeffCnt()==0) {
      if(premiseCollapsingInequality->isRefutation()) {
	c = premiseCollapsingInequality;
	break;
      }
      ASS(premiseCollapsingInequality->isTautology());
    }
    else {      
      Constraint* newC = Constraint::resolve(bs.bound.var, *c, *premiseCollapsingInequality);      
      newC->markCollapsing();
      c = newC;
    }
  }
  bi.setCachedCollapsingInequality(c.ptr());
  result = c;
}

/**
 * Into @c result assign conflict collapsing inequality between the bounds
 * on variable @c v.
 *
 * There must be a conflict between bounds on the variable.
 *
 * The particular conflict is selected by the @c _conflictSelector.
 */
void BoundsArray::getConflictCollapsingInequality(Var v, ConstraintRCPtr& result) const
{
  CALL("BoundsArray::getConflictCollapsingInequality/2");
  ASS(hasConflict(v));

  size_t leftIdx, rightIdx;
  ASS(_conflictSelector);
  _conflictSelector->getConflictIndexes(v, leftIdx, rightIdx);

  getConflictCollapsingInequality(v, leftIdx, rightIdx, result);
}

/**
 * Into @c result assign conflict collapsing inequality between the @c leftIdx -th
 * left bound and @c rightIdx -th right bound on variable @c v.
 *
 * There must be a conflict between the two specified bounds.
 */
void BoundsArray::getConflictCollapsingInequality(Var v, size_t leftIdx, size_t rightIdx, ConstraintRCPtr& result) const
{
  CALL("BoundsArray::getConflictCollapsingInequality/4");

  BoundId leftBound(v, true);
  BoundId rightBound(v, false);
  ASS(getBounds(leftBound)[leftIdx].hasConflictWith(getBounds(rightBound)[rightIdx], true));

  ConstraintRCPtr collapsingLeft, collapsingRight;
  tryGetCollapsingInequality(leftBound, leftIdx, collapsingLeft);
  tryGetCollapsingInequality(rightBound, rightIdx, collapsingRight);
  //at least one of the two conflicting bounds should come from bound propagation
  //(we do not create conflicts by value assignments)
  ASS(collapsingLeft || collapsingRight);
  if(!collapsingLeft) {
    result = collapsingRight;
  }
  else if(!collapsingRight) {
    result = collapsingLeft;
    }
  else {
    Constraint* res = Constraint::resolve(v, *collapsingLeft, *collapsingRight);
    res->markCollapsing();
    result = res;    
  }
}

/**
 * Remove all bounds with @c BoundInfo::depth() greater than @c maxDepth.
 */
void BoundsArray::backtrack(DecisionLevel maxDepth)
{
  CALL("BoundsArray::backtrack");

  while(_updateQueue.isNonEmpty() && getBounds(_updateQueue.back().bound)[_updateQueue.back().boundDepth].depth()>maxDepth) {
    _updateQueue.pop_back();
  }

#if VDEBUG
  UpdateQueue::Iterator uqit(_updateQueue);
  while(uqit.hasNext()) {
    const UpdateInfo& ui = uqit.next();
    ASS_LE(getBounds(ui.bound)[ui.boundDepth].depth(), maxDepth);
  }
#endif

  size_t sz = varCnt();
  for(size_t i=0; i<sz; i++) {
    backtrackStack(getBounds(BoundId(i, true)), maxDepth);
    backtrackStack(getBounds(BoundId(i, false)), maxDepth);
  }  
}

/**
 * From @c s remove all bounds with @c BoundInfo::depth() greater than @c maxDepth.
 */
void BoundsArray::backtrackStack(BoundStack& s, DecisionLevel maxDepth)
{
  CALL("BoundsArray::backtrackStack");

  while(s.isNonEmpty() && s.top().depth()>maxDepth) {
    s.pop();
  }
}

}
#endif //GNUMP
