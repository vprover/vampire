/**
 * @file VariableSelector.cpp
 * Implements class VariableSelector.
 */
#if GNUMP

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Random.hpp"

#include "Kernel/Signature.hpp"

#include "Shell/Options.hpp"

#include "BoundsArray.hpp"
#include "ConflictingVariableSelector.hpp"
#include "LookAheadVariableSelector.hpp"
#include "Solver.hpp"

#include "VariableSelector.hpp"

#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Lib;
using namespace Shell;

VariableSelector::VariableSelector(Solver& solver)
: _solver(solver), _bounds(solver.getBounds()), _varCnt(solver.varCnt())
{}

bool VariableSelector::isEligible(Var v)
{
  CALL("VariableSelector::isEligible");

  return _solver.isProblemVar(v) && !_bounds.hasTightBound(v);
}

bool VariableSelector::getNextEligibleVariable(Var firstPossible, Var& res)
{
  CALL("VariableSelector::getNextEligibleVariable");

  if(firstPossible>=_bounds.varCnt()) {
    return false;
  }

  res = firstPossible;

  while(!isEligible(res)) {
    res++;
    if(res==_bounds.varCnt()) {
      return false;
    }
    ASS_L(res,_bounds.varCnt());
  }
  return true;
}

class FirstVariableSelector : public VariableSelector
{
public:
  FirstVariableSelector(Solver& s) : VariableSelector(s) {}

  virtual Var getNextVariable()
  {
    CALL("FirstVariableSelector::getNextVariable");

    Var res;
    ALWAYS(getNextEligibleVariable(0, res));
    TRACE("tkv_vselect",tout<<"Picking variable "<<env.signature->varName(res)<<" as a decision point";);
    return res;
  }
};

class RandomVariableSelector : public VariableSelector
{
public:
  RandomVariableSelector(Solver& s) : VariableSelector(s) {}

  virtual Var getNextVariable()
  {
    CALL("RandomVariableSelector::getNextVariable");

    Var varCnt = _bounds.varCnt();
    Var res;
    static const unsigned randomAttempts = 5;
    for(unsigned i=0; i<randomAttempts; i++) {
      res = Random::getInteger(varCnt);
      if(isEligible(res)) {
	TRACE("tkv_vselect",tout<<"Randomly picking variable "<<env.signature->varName(res)<<" as a decision point";);
	return res;
      }
    }
    if(!getNextEligibleVariable(res, res)) {
      ALWAYS(getNextEligibleVariable(0, res));
    }
    TRACE("tkv_vselect",tout<<"Picking variable "<<env.signature->varName(res)<<" as a decision point by linear search with random origin";);
    return res;
  }
};

class TightestBoundVariableSelector : public VariableSelector
{
public:
  TightestBoundVariableSelector(Solver& s) : VariableSelector(s) {}

  bool getBoundDistance(Var v, BoundNumber& dist)
  {
    CALL("TightestBoundVariableSelector::getBoundDistance");

    ASS(!_bounds.hasTightBound(v));
    BoundNumber left, right;
    if(!_bounds.getBound(BoundId(v, true), left) || !_bounds.getBound(BoundId(v, false), right)) {
      return false;
    }
    ASS_L(left,right);
    dist = right-left;
    return true;
  }

  virtual Var getNextVariable()
  {
    CALL("TightestBoundVariableSelector::getNextVariable");

    bool foundFullyBound = false;
    Var notFullyBound; //we'll use this variable if there is no fully bound one
    Var best = 0;
    BoundNumber bestDist;
    BoundNumber currDist;

    Var varCnt = _solver.varCnt();
    for(Var var=0; var<varCnt; var++) {
      if(!isEligible(var)) {
	continue;
      }
      if(getBoundDistance(var, currDist)) {
	if(!foundFullyBound) {
	  foundFullyBound = true;
	  best = var;
	  bestDist = currDist;
	}
	else if(bestDist>currDist) {
	  best = var;
	  bestDist = currDist;
	}
      }
      else {
	notFullyBound = var;
      }
    }
    if(!foundFullyBound) {
      return notFullyBound;
    }
    TRACE("tkv_vselect",tout<<"Tightest variable selection "<<env.signature->varName(best)<<" as the next variable\n";);
    return best;
  }
};

class UnusedVariableSelector : public VariableSelector
{
  typedef Stack<Var> VarStack;
public:
  UnusedVariableSelector(Solver& s, VariableSelector* inner) : VariableSelector(s), _inner(inner)
  {
    CALL("UnusedVariableSelector::UnusedVariableSelector");

    Var varCnt = s.varCnt();
    for(Var v=0; v<varCnt; v++) {
      _unusedVars.push(v);
    }
  }

  virtual Var getNextVariable()
  {
    CALL("UnusedVariableSelector::getNextVariable");

    VarStack::Iterator vit(_unusedVars);
    while(vit.hasNext()) {
      Var v = vit.next();
      if(isEligible(v)) {
	vit.del();
	TRACE("tkv_vselect",tout<<"Unused variable selected: "<< env.signature->varName(v)<<"\n";);
	return v;
      }
    }
    return _inner->getNextVariable();
  }
private:
  VarStack _unusedVars;
  ScopedPtr<VariableSelector> _inner;
};

VariableSelector* VariableSelector::create(Solver& s, Options& opt)
{
  VariableSelector* res;
  switch(opt.bpVariableSelector()) {
  case Options::VS_CONFLICTING:
    res = new ConflictingVariableSelector(s, false);
    break;
  case Options::VS_CONFLICTING_AND_COLLAPSING:
    res = new ConflictingVariableSelector(s, true);
    break;
  case Options::VS_FIRST:
    res = new FirstVariableSelector(s);
    break;
  case Options::VS_LOOK_AHEAD:
    res = new LookAheadVariableSelector(s);
    break;
  case Options::VS_RANDOM:
    res = new RandomVariableSelector(s);
    break;
  case Options::VS_RECENTLY_CONFLICTING:
    res = new RecentlyConflictingVariableSelector(s, false);
    break;
  case Options::VS_RECENTLY_COLLAPSING:
    res = new RecentlyConflictingVariableSelector(s, true);
    break;
  case Options::VS_TIGHTEST_BOUND:
    res = new TightestBoundVariableSelector(s);
    break;
  default:
    ASSERTION_VIOLATION;
  }
  if(opt.bpSelectUnusedVariablesFirst()) {
    res = new UnusedVariableSelector(s, res);
  }
  return res;
}


}
#endif //GNUMP

