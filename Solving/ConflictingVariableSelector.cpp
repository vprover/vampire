/**
 * @file ConflictingVariableSelector.cpp
 * Implements class ConflictingVariableSelector.
 */

#if GNUMP

#include <limits>

#include "Lib/Environment.hpp"

#include "Kernel/Signature.hpp"

#include "Solver.hpp"

#include "ConflictingVariableSelector.hpp"

#undef LOGGING
#define LOGGING 0

namespace Solving
{

using namespace Lib;
using namespace Kernel;

ConflictAwareVariableSelector::ConflictAwareVariableSelector(Solver& s)
 : VariableSelector(s)
{
  CALL("ConflictAwareVariableSelector::ConflictAwareVariableSelector");

  _onConflictSD = s.onConflict.subscribe(this, &ConflictingVariableSelector::conflictHandler);
}

void ConflictAwareVariableSelector::conflictHandler(Var v, Constraint* constr)
{
  CALL("ConflictAwareVariableSelector::conflictHandler");

  onConflict(v, constr);
}

/////////////////////////////////
// ConflictingVariableSelector

ConflictingVariableSelector::ConflictingVariableSelector(Solver& s, bool considerCollapsing)
 : ConflictAwareVariableSelector(s), _considerCollapsing(considerCollapsing), _varStats(s.varCnt())
{}


Var ConflictingVariableSelector::getNextVariable()
{
  CALL("ConflictingVariableSelector::getNextVariable");

  Var best;
  ALWAYS(getNextEligibleVariable(0, best));

  Var cur = best;
  while(getNextEligibleVariable(cur+1, cur)) {
    if(secondIsBetter(best, cur)) {
      best = cur;
    }
  }
  return best;
}

bool ConflictingVariableSelector::secondIsBetter(Var v1, Var v2)
{
  CALL("ConflictingVariableSelector::secondIsBetter");

  const VarStats& vs1 = _varStats[v1];
  const VarStats& vs2 = _varStats[v2];

  if(_considerCollapsing) {
    return vs1._conflictCnt+vs1._conflictCollapsingClauseAppearances < vs2._conflictCnt+vs2._conflictCollapsingClauseAppearances;
  }
  else {
    return vs1._conflictCnt<vs2._conflictCnt ||
	(vs1._conflictCnt==vs2._conflictCnt &&
	    vs1._conflictCollapsingClauseAppearances < vs2._conflictCollapsingClauseAppearances);
  }
}

void ConflictingVariableSelector::onConflict(Var v, Constraint* constr)
{
  CALL("ConflictingVariableSelector::onConflict");

  _varStats[v]._conflictCnt++;

  Constraint::CoeffIterator cit = constr->coeffs();
  while(cit.hasNext()) {
    const Constraint::Coeff& coeff = cit.next();
    _varStats[coeff.var]._conflictCollapsingClauseAppearances++;
  }
}

/////////////////////////////////////////
//VSIDS variable selector
VSIDSVariableSelector::VSIDSVariableSelector(Solver& s, unsigned int iterationsToDecay) :
    ConflictAwareVariableSelector(s), _iterationToDecay(iterationsToDecay), _varList(s.varCnt()),_orderList(s.varCnt())
{
CALL("VSIDSVariableSelector::VSIDSVariableSelector");
}

void VSIDSVariableSelector::onConflict(Var v, Constraint* constr)
{
    CALL("VSIDSVariableSelector::onConflict()");
    //check if we have first to decay

    _varList[v]._conflictCount++;

    Constraint::CoeffIterator coefIte = constr->coeffs();
    while(coefIte.hasNext()) {
	const Constraint::Coeff& c = coefIte.next();
	_varList[c.var]._conflictCollapsingAppearenceCount++;
    }

}

Var VSIDSVariableSelector::getNextVariable()
{
    Var best;
    return best;
}


/////////////////////////////////////////
// RecentlyConflictingVariableSelector

const Var RecentlyConflictingVariableSelector::VAR_NIL = std::numeric_limits<Var>::max();

RecentlyConflictingVariableSelector::RecentlyConflictingVariableSelector(Solver& s, bool considerCollapsing)
 : ConflictAwareVariableSelector(s), _considerCollapsing(considerCollapsing), _varList(s.varCnt())
{
  CALL("RecentlyConflictingVariableSelector::RecentlyConflictingVariableSelector");

  Var sz = s.varCnt();
  if(sz==0) {
    return;
  }

  //build the list in some order (here it is ascending but that does not matter.)
  _varList[0]._prev = VAR_NIL;
  _varList[sz-1]._next = VAR_NIL;
  if(sz>1) {
    _varList[1]._prev = 0;
    _varList[sz-2]._next = sz-1;
  }
  for(Var i=1; i<sz-1; i++) {
    _varList[i-1]._next = i;
    _varList[i+1]._prev = i;
  }
  _first = 0;
}

Var RecentlyConflictingVariableSelector::getNextVariable()
{
  CALL("RecentlyConflictingVariableSelector::getNextVariable");

#if VDEBUG
  size_t cnt = 0;
#endif
  Var v = _first;

  for(;;) {
    if(isEligible(v)) {
      return v;
    }
    v = _varList[v]._next;
    ASS_NEQ(v, VAR_NIL); //there must always be at least one eligible variable
#if VDEBUG
    cnt++;
    ASS_L(cnt, _solver.varCnt()); //we visit each variable at most once
#endif
  }
}

void RecentlyConflictingVariableSelector::onConflict(Var v, Constraint* constr)
{
  CALL("RecentlyConflictingVariableSelector::onConflict");

  if(_considerCollapsing) {
    Constraint::CoeffIterator cit = constr->coeffs();
    while(cit.hasNext()) {
      Var colVar = cit.next().var;
      makeRecent(colVar);
    }
  }
  else {
    makeRecent(v);
  }
}

void RecentlyConflictingVariableSelector::makeRecent(Var v)
{
  CALL("RecentlyConflictingVariableSelector::makeRecent");

  if(v==_first) {
    return;
  }

  Var prev = _varList[v]._prev;
  Var next = _varList[v]._next;

  if(prev!=VAR_NIL) {
    ASS_EQ(_varList[prev]._next, v);
    _varList[prev]._next = next;
  }
  if(next!=VAR_NIL) {
    ASS_EQ(_varList[next]._prev, v);
    _varList[next]._prev = prev;
  }

  _varList[v]._prev = VAR_NIL;
  _varList[v]._next = _first;
  _varList[_first]._prev = v;

  _first = v;
}


}

#endif //GNUMP

