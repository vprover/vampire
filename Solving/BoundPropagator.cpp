/**
 * @file BoundPropagator.cpp
 * Implements class BoundPropagator.
 */
#if GNUMP
#include "Lib/Exception.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Constraint.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Solver.hpp"
#include "BoundPropagator.hpp"

#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Lib;
using namespace Shell;

BoundPropagator* BoundPropagator::create(Solver& s, Options& opt)
{
  return new BoundPropagator(s, opt);
}

BoundPropagator::BoundPropagator(Solver& solver, Options& opt)
  : _solver(solver),
    _bounds(solver.getBounds()),
    _useCollapsingConstraints(opt.bpCollapsingPropagation()),
    _updatesByOneConstraint(opt.bpUpdatesByOneConstraint()),
    _varCnt(solver.varCnt())
{
  CALL("BoundPropagator::BoundPropagator");
}

/**
 * Functor that maps a bound into iterator on constraints through which
 * the bound can be propagated
 */
struct BoundPropagator::BoundConstraintIteratorFn
{
  BoundConstraintIteratorFn(BoundPropagator& parent) : _parent(parent) {}

  DECL_RETURN_TYPE(V2CIndex::Iterator);
  OWN_RETURN_TYPE operator()(const BoundId& bound) {
    return _parent._constrByBound.getConsraintsWithComplementary(bound);
  }

  BoundPropagator& _parent;
};

BoundSuggestionResult BoundPropagator::propagateDecisionPoints()
{
  CALL("BoundPropagator::propagateDecisionPoints");

  TimeCounter tc(TC_BOUND_PROPAGATION);

  static BoundIdStack toDo;

  BoundSuggestionResult res = BS_NONE;

  BoundsArray::UpdateQueue& que = _bounds.getUpdateQueue();
  collectUpdated(que, toDo);

  ConstraintIterator cit = pvi( getUniquePersistentIterator(
      getMapAndFlattenIterator(
	  BoundIdStack::Iterator(toDo),
	  BoundConstraintIteratorFn(*this)) ) );
  while(cit.hasNext()) {
    Constraint& c = *cit.next();
    BoundSuggestionResult localRes = propagateBounds(c, true);
    if(localRes>res) {
      res = localRes;
    }
  }
  return res;
}

/**
 * Propagate bound updates that are in the update queue of the
 * @c BoundsArray object in @c _solver, and empty the queue afterward
 */
BoundSuggestionResult BoundPropagator::propagate()
{
  CALL("BoundPropagator::propagate");

  TimeCounter tc(TC_BOUND_PROPAGATION);

  BoundSuggestionResult res = BS_NONE;
  /*
   res = propagateDecisionPoints();
   if(res==BS_CONFLICT) {
   //we have already reached a conflict
   return BS_CONFLICT;
   }
   */
  static BoundIdStack toDo;

  static BoundsArray::UpdateQueue backup;

  BoundsArray::UpdateQueue& que = _bounds.getUpdateQueue();
  while (que.isNonEmpty()) {
    collectUpdated(que, toDo);
    backup.reset();
    backup.pushBackFromIterator(
	    BoundsArray::UpdateQueue::FrontToBackIterator(que));
    que.reset();

#if 1
    ConstraintIterator cit = pvi(
	    getUniquePersistentIterator(
		    getMapAndFlattenIterator(BoundIdStack::Iterator(toDo),
			    BoundConstraintIteratorFn(*this))));
#else
    ConstraintList::Iterator cit(_solver.aliveConstraints());
#endif
    while (cit.hasNext()) {
      Constraint& c = *cit.next();
      BoundSuggestionResult localRes = propagateBounds(c);
      if (localRes == BS_CONFLICT) {
	//we don't propagate further when we reach a conflict
	que.pushFrontFromIterator(
		BoundsArray::UpdateQueue::BackToFrontIterator(backup));
	return localRes;
      }
      if (localRes > res) {
	res = localRes;
      }
    }
  }
  return res;
}

/**
 * Remove records from @c _bounds.getUpdateQueue() and add them to
 * the @c updatedBounds stack
 */
void BoundPropagator::collectUpdated(BoundsArray::UpdateQueue& que, BoundIdStack& acc, bool tightBoundsOnly)
{
  CALL("BoundPropagator::collectUpdated");

  acc.reset();
  BoundsArray::UpdateQueue::Iterator qit(que);
  while(qit.hasNext()) {
    const BoundsArray::UpdateInfo& inf = qit.next();
    if(tightBoundsOnly && _bounds.hasTightBound(inf.bound.var)) {
      continue;
    }
    acc.push(inf.bound);
  }
}

/**
 * Perform bound propagation with constraint @c constr.
 */
BoundSuggestionResult BoundPropagator::propagateBounds(Constraint& constr, bool tightBoundsOnly)
{
  CALL("BoundPropagator::propagateBounds(Constraint*)");

  bool unboundedFound = false;
  Var unboundedVar;

  Constraint::CoeffIterator cit = constr.coeffs();
  TRACE("tkv_constraint", tout<<constr.toString()<<"\n";);
  while(cit.hasNext()) {
    const Constraint::Coeff& coeff = cit.next();
    if(coeff.value==CoeffNumber::zero())
      return BS_NONE;

    Var currVar = coeff.var;

    bool isUnbounded;
    if(tightBoundsOnly) {
      isUnbounded = _bounds.hasTightBound(currVar);
    }
    else {
      bool leftBoundNeeded = coeff.isNegative();
      isUnbounded = _bounds.isUnbounded(BoundId(currVar, leftBoundNeeded));
    }

    if(!isUnbounded) {
      continue;
    }
    if(unboundedFound) {
      //if there are two unbounded variables in a constraint, no bound can be inferred
      return BS_NONE;
    }
    unboundedVar = currVar;
    unboundedFound = true;
  }

  if(unboundedFound) {
    return propagateBounds(constr, unboundedVar);
  }

  //all variables are bounded, so we may try to infer a new bound on all of them
  BoundSuggestionResult res = BS_NONE;
  cit = constr.coeffs();
  while(cit.hasNext()) {
    Constraint::Coeff coeff = cit.next();
    BoundSuggestionResult localRes = propagateBounds(constr, coeff.var);
    if(localRes!=BS_NONE) {
      res = localRes;
      if(res==BS_CONFLICT) {
	//when we have a conflict, we don't continue with propagation
	break;
      }
    }
  }
  return res;
}

/**
 * Perform bound propagation trying to improve the bound on variable
 * @c v.
 */
BoundSuggestionResult BoundPropagator::propagateBounds(Constraint& constr, Var v)
{
  CALL("BoundPropagator::propagateBounds(Constraint*,Var)");
  ASS_NEQ(constr.type(),CT_EQ);

  CoeffNumber vCoeff = CoeffNumber::zero();
  bool resultLeft;
  bool nonStrict = constr.type()==CT_GREQ;

  typedef BoundJustification::BoundSpec BoundSpec;
  typedef Stack<BoundSpec> BoundSpecStack;

  static BoundSpecStack boundSpecs;
  boundSpecs.reset();

  Constraint::CoeffIterator cit = constr.coeffs();

  static BoundNumber boundValue;
  boundValue = BoundNumber(constr.freeCoeff());
  static BoundNumber boundVal;

  while(cit.hasNext()) {
    const Constraint::Coeff& coeff = cit.next();
    Var currVar = coeff.var;
    if(currVar==v) {
      vCoeff = coeff.value;
      resultLeft = coeff.isPositive();
      continue;
    }
    //if(coeff.value==CoeffNumber::zero())
    //continue;
    ASS_REP2(coeff.value!=CoeffNumber::zero(), constr.toString(), currVar);
    bool leftBoundNeeded = coeff.isNegative();
    BoundId srcBound(currVar, leftBoundNeeded);
    bool boundStrict;
    if(!_bounds.getBound(srcBound, boundVal, boundStrict)) {
      //if we have unbounded non-target variable, we cannot infer any
      //bound from the constraint
      return BS_NONE;
    }
    nonStrict &= !boundStrict;
    boundValue -= boundVal*coeff.value;
    LOG("tkv_bK", "value "<<env.signature->varName(currVar)<<" " <<boundValue);


    ASS(_bounds.getBounds(srcBound).isNonEmpty());
    size_t boundIndex = _bounds.getBounds(srcBound).size()-1;
    boundSpecs.push(BoundSpec(srcBound, boundIndex));
  }

  ASS_NEQ(vCoeff, CoeffNumber::zero());

  BoundId newBoundId(v, resultLeft);

  size_t boundsByThisConstraint = _bounds.countBoundsByConstraintOnCurrentLevel(newBoundId, constr);

  if(_useCollapsingConstraints && boundsByThisConstraint!=0
      && _bounds.isBoundedByCollapsingConstraintOnCurrentLevel(newBoundId)) {
    //If variable was already bound at this level using @c constr, and there
    //is also already a collapsing constraint, we do not continue with bound
    //propagation here to avoid cycles.
    return BS_NONE;
  }
  if(boundsByThisConstraint>_updatesByOneConstraint-1) {
    return BS_NONE;
  }

  if(vCoeff!=CoeffNumber::zero())
    boundValue/=BoundNumber(vCoeff);

  BoundInfo bi;
  bi.setValue(boundValue);
  bi.setStrict(!nonStrict);
  bi.justification().setParent(&constr);
  bi.justification().initPropagatedBounds(BoundSpecStack::Iterator(boundSpecs));

  BoundSuggestionResult res = _bounds.suggestBound(newBoundId, bi);
  if(res!=BS_NONE) {
    _bounds.getSolver().getStats().propagatedBounds++;
  }
  if(_useCollapsingConstraints && res==BS_IMPROVEMENT && boundsByThisConstraint!=0) {
    //If variable was already bound at this level using @c constr, and we managed to
    //use it again to improve the bound, we may have a bound improvement cycle.
    //Therefore we generate a collapsing inequality and try to improve the bound with
    //it.
    //We generate a collapsing inequality only once on each level to avoid cycles.
    ConstraintRCPtr collapsingConstr;
    _bounds.tryGetCollapsingInequality(newBoundId, collapsingConstr);
    LOG("tkv_colapsing","Bound collapsing constr generated: "<<collapsingConstr->toString());
    res = propagateBounds(*collapsingConstr);
    LOG("tkv_colapsing","Collapsing constr propagation done");
  }
  return res;
}

/**
 * Register constraint so that bound propagation will be performed with it
 */
void BoundPropagator::registerConstraint(Constraint* constr)
{
  CALL("BoundPropagator::registerConstraint");

  _constrByBound.insert(constr);
}

}
#endif
