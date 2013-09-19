/**
 * @file Solver.cpp
 * Implements class Solver.
 */
#if GNUMP

#include "Forwards.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/List.hpp"
#include "Lib/Timer.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Assignment.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "AssignmentSelector.hpp"
#include "ConflictSelector.hpp"
#include "VariableSelector.hpp"

#include "Solver.hpp"

#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Lib;
using namespace Kernel;
using namespace Shell;

struct Solver::RefutationFoundException
{
  RefutationFoundException(Constraint* refutation) : refutation(refutation) {}
  RefutationFoundException(ConstraintRCPtr& refutation) : refutation(refutation) {}

  ConstraintRCPtr refutation;
};

/**
 * Create the solver objects.
 *
 * Statistics of the solver run and also its outcome will be
 * stored into the @c stats obejct.
 */
Solver::Solver(size_t varCnt, Options& opt, Statistics & stats)
 : _stats(stats),
   _varCnt(varCnt),
   _bounds(*this),
   _varSelector(VariableSelector::create(*this, opt)),
   _asgSelector(AssignmentSelector::create(*this, opt)),
   _propagator(BoundPropagator::create(*this, opt)),
   _problemVariables(varCnt),
   _inputConstraints(0),
   _inputConstraintsRC(0),
   _aliveConstraints(0),
   _aliveConstraintsRC(0),
   _haveForcedDecision(false)
{
  _problemVariables.init(varCnt, false);
  _bounds.assignConflictSelector(ConflictSelector::create(*this, opt));

  //reset counters of vars and constraints passed to the solver
  //(they are updated in Solver::load())
  _stats.preprocessedConstraints = 0;
  _stats.preprocessedVariables = 0;
}

Solver::~Solver()
{
  CALL("Solver::~Solver");

  _inputConstraints->destroy();
  _inputConstraintsRC->destroy();
  _aliveConstraints->destroy();
  _aliveConstraintsRC->destroy();
}
/**
 * Load constraints into the solver.
 *
 * The constraints must be either of type @c CT_GR or @c CT_GREQ.
 *
 * The solver takes ownership over the @c constraints list and the objects inside it.
 */
void Solver::load(ConstraintRCList* constraints)
{
  CALL("Solver::load");

  ConstraintRCList::Iterator cit(constraints);
  while(cit.hasNext()) {
    ConstraintRCPtr c(cit.next());
    ConstraintRCList::push(c, _inputConstraintsRC);
    ConstraintList::push(c.ptr(), _inputConstraints);

    _stats.preprocessedConstraints++;

    Constraint::CoeffIterator coeffIt(c->coeffs());
    while(coeffIt.hasNext()) {
      Var v = coeffIt.next().var;
      if(!_problemVariables[v]) {
	_stats.preprocessedVariables++;
      }
      _problemVariables[v] = true;
    }
  }
}

/**
 * Put bounds contained in the input constraints into @c _bounds
 */
void Solver::collectInputBounds()
{
  CALL("Solver::collectInputBounds");

  ConstraintList::Iterator cit(_inputConstraints);
  while(cit.hasNext()) {
    Constraint* c = cit.next();
    ASS_NEQ(c->type(),CT_EQ);

    size_t coeffCnt = c->coeffCnt();
    if(coeffCnt==0) {
      if(c->isRefutation()) {
    	  throw RefutationFoundException(c);
      }
      ASS(c->isTautology());
    }
    else if(coeffCnt==1) {
      Constraint::CoeffIterator coeffIt = c->coeffs();
      ALWAYS(coeffIt.hasNext());
      const Constraint::Coeff& coeff = coeffIt.next();
      ASS(!coeffIt.hasNext());

      bool leftBound = coeff.isPositive();
      BoundId newBoundId(coeff.var, leftBound);
      ASS_NEQ(coeff.value, CoeffNumber::zero());
      BoundNumber boundVal;
      if(c->freeCoeff()==CoeffNumber::zero() || coeff.value == CoeffNumber::zero()){
    	  boundVal = BoundNumber(CoeffNumber::zero());
      }
      else{
    	  BoundNumber boundVal = BoundNumber(c->freeCoeff())/coeff.value;
      }
      BoundInfo bi(boundVal, c->type()==CT_GR);
      bi.justification().setParent(c);
      _bounds.suggestBound(newBoundId, bi);
    }
    else {
      retainConstraint(c);
    }
  }

}

void Solver::retainConstraint(Constraint* c)
{
  CALL("Solver::retainConstraint");

  ConstraintList::push(c, _aliveConstraints);
  ConstraintRCList::push(ConstraintRCPtr(c), _aliveConstraintsRC);
  TRACE("tkv_alive", tout<<c->toString()<<endl;);
  _propagator->registerConstraint(c);
}

/**
 * Return true if all variables have tight bounds
 *
 * If true is returned, the solving is done and the problem is satisfiable.
 */
bool Solver::haveFullAssignment()
{
  CALL("Solver::haveFullAssignment");

  size_t vcnt = varCnt();
  for(Var v=0; v<vcnt; v++) {
    if(isProblemVar(v) && !_bounds.hasTightBound(v)) {
      return false;
    }
  }
  return true;
}

/**
 * Return the highest decision level of a variable present in
 * @c conflictCollapsingConstraint.
 *
 * The @c conflictCollapsingConstraint constraint can contain only
 * decision variables.
 */
DecisionLevel Solver::getHighestDecisionLevel(Constraint& conflictCollapsingConstraint)
{
  CALL("Solver::getHighestDecisionLevel");

  DecisionLevel res = -1;
  Constraint::CoeffIterator cit(conflictCollapsingConstraint.coeffs());
  while(cit.hasNext()) {
    Var v = cit.next().var;
    DecisionLevel lev = _decStack.getVarLevel(v);
    ASS_NEQ(lev, -1); //collapsing constraint should contain only decision variables
    if(lev>res) {
      res = lev;
    }
  }
  return res;
}

/**
 * Check whether there are any conflicts and recover from them.
 * If the recovery is not possible, the problem is unsatisfiable
 * and false is returned by this function.
 */
void Solver::handleConflicts()
{
  CALL("Solver::handleConflicts");

  TimeCounter tc(TC_HANDLING_CONFLICTS);

  BoundsArray::ConflictSet& cset = _bounds.getConflictSet();
  if(cset.isEmpty()) {
    return;
  }

  static Stack<ConstraintRCPtr> collapsingConstraints;
  collapsingConstraints.reset();

  TRACE("tkv_colapse", tout<<"handle conflict"<<endl;);
  VarIterator conflictVars = cset.iterator();
  DecisionLevel tgtDepth = -1;
  Var conflictVar;
  while(conflictVars.hasNext()) {
    conflictVar = conflictVars.next();
    ConstraintRCPtr colConstr;
    _bounds.getConflictCollapsingInequality(conflictVar, colConstr);
    LOG("tkv_colapse","Collapsing inequality: "<<colConstr->toString());

   TRACE("tkv_colapse", tout<<colConstr->toString(););
    if(colConstr->isTautology()) {
      LOG("tkv_colapse","Collapsing inequality is a tautology!");
      throw NumberImprecisionException();
    }
    if(colConstr->isRefutation()) {
      //std::cout<<colConstr->toString()<<std::endl;
      throw RefutationFoundException(colConstr);
    }
    ASS_REP(colConstr->coeffCnt()>0, colConstr->toString());

    collapsingConstraints.push(colConstr);
    DecisionLevel localTgtDepth = getHighestDecisionLevel(*colConstr)-1;
    if(localTgtDepth>tgtDepth) {
      tgtDepth = localTgtDepth;
    }
  }
  ASS_GE(tgtDepth,0);
  ASS_L(tgtDepth,getDepth());

  //Variables in collapsing constraints may come only from decision points
  //(if bound comes from elsewhere, the variable is resolved away with the
  //premise clause). On level 0 there are no decision points, so the
  //only collapsing constraint on that level can be refutation (which are
  //being handled earlier).
  ASS_G(getDepth(),0);

  cset.reset();

  Var lastDecVar;
  if(env.options->backjumpTargetIsDecisionPoint()) {
    lastDecVar = _decStack.getDecisionVar(tgtDepth+1);
  }
  else {
    lastDecVar = _decStack.getDecisionVar(getDepth());
  }
  onConflict.fire(conflictVar, collapsingConstraints.top().ptr());

  backtrack(tgtDepth);

  bool first = true;
  BoundSuggestionResult propRes = BS_NONE;
  while(collapsingConstraints.isNonEmpty()) {
    ConstraintRCPtr constr = collapsingConstraints.pop();
    propRes = _propagator->propagateBounds(*constr);
    if(propRes==BS_NONE && first) {
      LOG("tkv_colapse","Collapsing inequality did not improve any bounds!");
      throw NumberImprecisionException();
    }
////    if(constr->coeffCnt()*_stats.retainedConstraints<Lib::env.timer->elapsedDeciseconds()*10) {
//    if(constr->coeffCnt()==2) {
//      _stats.retainedConstraints++;
//      retainConstraint(constr.ptr());
//    }
    if(propRes==BS_CONFLICT) {
      break;
    }
    first=false;
  }
  ASS(propRes==BS_CONFLICT || _bounds.getConflictSet().isEmpty());
  if(propRes!=BS_CONFLICT &&
      ( env.options->bpPropagateAfterConflict() ||
       (_bounds.hasTightBound(lastDecVar) && haveFullAssignment()) ) ) {
//  if(propRes!=BS_CONFLICT && _bounds.hasTightBound(lastDecVar)) {
    //Sometimes the collapsing constraint propagation may create a tight bound
    //on the last unbound variable. In that case we would finish the algorithm,
    //thinking that the problem is satisfiable, even though there might be a conflict
    //caused by the newly added tight bound.
    //On the other hand, we do not want to do the bound propagation unless the
    //tight bound makes us, because it (for some reason) makes the algorithm go
    //crazy.
    LOG("tkv_conflict","Propagating input inequalities after a conflict");
    propRes = _propagator->propagate();
    LOG("tkv_conflict","Propagating input inequalities after a conflict done");
  }

  setForcedDecision(lastDecVar);

  handleConflicts(); //handle conflicts possibly introduced by propagation of collapsing constraints
}

void Solver::backtrack(DecisionLevel lev)
{
  CALL("Solver::backtrack");
  ASS_GE(lev,0);
  ASS_L(lev,getDepth());

  if(lev<getDepth()-1) {
    _stats.longBacktracks++;
  }

  _decStack.backtrack(lev);
  _bounds.backtrack(lev);
  _stats.backtracks++;
}

void Solver::makeDecisionPoint(Var v, const BoundNumber& val)
{
  CALL("Solver::makeDecisionPoint");

  _decStack.addDecision(v);
  ASS(!_bounds.hasTightBound(v)); //there is no point in doing assignments to variables with tight bounds
  _bounds.makeDecisionAssignment(v, val);
  ASS(_bounds.hasTightBound(v));

  if(_stats.maxDecisionDepth<getDepth()) {
    _stats.maxDecisionDepth=getDepth();
  }
}

/**
 * Set the forced decision to @c v.
 */
void Solver::setForcedDecision(Var v)
{
  CALL("Solver::setForcedDecision");

  _haveForcedDecision = true;
  _forcedDecisionVar = v;
}

/**
 * If there is a forced decision choice, assign the decision variable
 * into @c v, remove the forced decision and return true. Otherwise
 * return false.
 */
bool Solver::tryUseForcedDecision(Var& v)
{
  CALL("Solver::tryUseForcedDecision");

  if(_haveForcedDecision) {
    _haveForcedDecision = false;
    if(!_bounds.hasTightBound(_forcedDecisionVar)) {
      v = _forcedDecisionVar;
      _stats.forcedDecisionPoints++;
      return true;
    }
  }
  return false;
}

void Solver::solve() {
  CALL("Solver::solve");

  TimeCounter tc(TC_SOLVING);

  if(usingPreciseNumbers()) {
    _stats.preciseUsed = true;
  }
  else {
    _stats.nativeUsed = true;
  }

  try {
    collectInputBounds();
    _propagator->propagate();
    handleConflicts();

    BoundNumber nextDecisionValue;

    while(!haveFullAssignment()) {
      Var nextDecisionVar;
      if(!tryUseForcedDecision(nextDecisionVar)) {
	TimeCounter tc(TC_VARIABLE_SELECTION);

	nextDecisionVar = _varSelector->getNextVariable();
	_stats.freeDecisionPoints++;

      }
      _asgSelector->getAssignment(nextDecisionVar, nextDecisionValue);
      TRACE("tkv_colapsing", tout<<nextDecisionVar<<endl;);
      makeDecisionPoint(nextDecisionVar, nextDecisionValue);
      _propagator->propagate();
      handleConflicts();
    }
  }
  catch(RefutationFoundException e) {
    _stats.terminationReason = Statistics::REFUTATION;
    //modified for the purpose of BP 
    //TODO fixme this should be used in the same manner as for vampire
    //std::cout<<"Refutation exception found here"<<std::endl;
    _stats.bpRefutation = e.refutation;
    return;
  }
  catch(TimeLimitExceededException e) {
      _stats.terminationReason = Statistics::TIME_LIMIT;
      return;
}
  size_t vcnt = varCnt();
  Assignment* asgn = new Assignment(vcnt);
  for(Var v=0; v<vcnt; v++) {
    if(isProblemVar(v)) {
      asgn->set(v, _bounds.getTightBound(v));
    }
  }

  if(!usingPreciseNumbers() && !asgn->isSatisfied(inputConstraints())) {
    delete asgn;
    throw NumberImprecisionException();
  }

  ASS(!_stats.satisfyingAssigment);
  _stats.satisfyingAssigment = asgn;
  _stats.terminationReason = Statistics::SATISFIABLE;

#if VDEBUG
  asgn->assertSatisfied(inputConstraints());
#endif
}


}
#endif //GNUMP

