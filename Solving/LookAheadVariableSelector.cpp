/**
 * @file LookAheadVariableSelector.cpp
 * Implements class LookAheadVariableSelector.
 */

#if GNUMP

#include "Lib/Comparison.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Int.hpp"

#include "Kernel/Constraint.hpp"
#include "Kernel/Signature.hpp"

#include "LookAheadVariableSelector.hpp"

#include "Solver.hpp"

#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Lib;
using namespace Kernel;

struct LookAheadVariableSelector::AheadData
{
  void reset()
  {
    constrMadeUnit = 0;
    constrMadeTightUnit = 0;
    constrWithVariable = 0;
  }

  unsigned constrMadeUnit;
  unsigned constrMadeTightUnit;
  unsigned constrWithVariable;
};

LookAheadVariableSelector::LookAheadVariableSelector(Solver& solver)
 : VariableSelector(solver)
{
  CALL("LookAheadVariableSelector::LookAheadVariableSelector");
}

Var LookAheadVariableSelector::getNextVariable()
{
  CALL("LookAheadVariableSelector::getNextVariable");

  Var best;
  AheadData bestAhead;
  ALWAYS(getNextEligibleVariable(0, best));
  populateAhead(best, bestAhead);

  AheadData curAhead;
  Var cur = best;
  while(getNextEligibleVariable(cur+1, cur)) {
    populateAhead(cur, curAhead);
    if(secondIsBetter(bestAhead, curAhead)) {
      best = cur;
      bestAhead = curAhead;
    }
  }

  LOG("tkv_vselect","LookAheadVariableSelector picks variable "<<env -> signature->varName(best)<<" as a decision point");
  return best;
}

bool LookAheadVariableSelector::secondIsBetter(AheadData& f, AheadData& s)
{
  CALL("LookAheadVariableSelector::secondIsBetter");

  Comparison res;
  res = Int::compare(f.constrMadeUnit, s.constrMadeUnit);
  if(res!=EQUAL) { return res==LESS; }
  res = Int::compare(f.constrMadeTightUnit, s.constrMadeTightUnit);
  if(res!=EQUAL) { return res==LESS; }
  res = Int::compare(f.constrWithVariable, s.constrWithVariable);
  if(res!=EQUAL) { return res==LESS; }
  return false;
}

void LookAheadVariableSelector::updateAhead(Var var, Constraint& constr, AheadData& d)
{
  CALL("LookAheadVariableSelector::updateAhead");

  if(!constr.hasVar(var)) {
    return;
  }
  d.constrWithVariable++;
  unsigned nonTight = 0;
  unsigned unbounded = 0;
  Constraint::CoeffIterator cit = constr.coeffs();
  while(cit.hasNext()) {
    const Constraint::Coeff& coeff = cit.next();
    if(coeff.var==var) {
      continue;
    }
    if(!_bounds.hasTightBound(coeff.var)) {
      nonTight++;
    }
    bool needsLeft = coeff.isNegative();
    if(_bounds.isUnbounded(BoundId(coeff.var, needsLeft))) {
      unbounded++;
    }
  }
  if(unbounded==1) {
    d.constrMadeUnit++;
  }
  if(nonTight==1) {
    d.constrMadeTightUnit++;
  }
}

void LookAheadVariableSelector::populateAhead(Var var, AheadData& d)
{
  CALL("LookAheadVariableSelector::populateAhead");

  d.reset();
  ConstraintList::Iterator cit(_solver.aliveConstraints());
  while(cit.hasNext()) {
    Constraint& c = *cit.next();
    updateAhead(var, c, d);
  }
}


}
#endif //GNUMP

