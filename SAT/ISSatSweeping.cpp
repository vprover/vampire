/**
 * @file ISSatSweeping.cpp
 * Implements class ISSatSweeping.
 */


#include "Lib/Random.hpp"

#include "ISSatSweeping.hpp"

namespace SAT
{

/**
 * @param varCnt maximal SAT variable number increased by one
 * @param solver SATSolver object whose state should we sweep for literal
 * 	equivalences. This solver should be in a satisfiable state without
 * 	any assumptions. We will add assumptions to probe for equivalences
 * 	and then retract them in the end.
 */
ISSatSweeping::ISSatSweeping(unsigned varCnt, SATSolver& solver)
: _varCnt(varCnt),
  _candidateVarPolarities(varCnt),
  _candidateGroupIndexes(varCnt),
  _equivalentVars(varCnt),
  _solver(solver)
{
  CALL("ISSatSweeping::ISSatSweeping");
  ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);
  ASS(!solver.hasAssumptions());

  _interestingVars.loadFromIterator(getRangeIterator(1u,varCnt));

  run();
}

/**
 * @param varCnt maximal SAT variable number increased by one
 * @param solver SATSolver object whose state should we sweep for literal
 * 	equivalences. This solver should be in a satisfiable state without
 * 	any assumptions. We will add assumptions to probe for equivalences
 * 	and then retract them in the end.
 * @param interestingVarIterator iterator on variables that are to be
 * 	examined for equivalences. Each variable can appear at most once.
 */
ISSatSweeping::ISSatSweeping(unsigned varCnt, SATSolver& solver, VirtualIterator<int> interestingVarIterator)
: _varCnt(varCnt),
  _candidateVarPolarities(varCnt),
  _candidateGroupIndexes(varCnt),
  _equivalentVars(varCnt),
  _solver(solver)
{
  CALL("ISSatSweeping::ISSatSweeping");
  ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);
  ASS(!solver.hasAssumptions());

  _interestingVars.loadFromIterator(interestingVarIterator);

  run();
}


/**
 * Return true if v1 and v2 are in the same candidate group. If at least
 * one of them is not in a candidate group, return false.
 */
bool ISSatSweeping::sameCandGroup(unsigned v1, unsigned v2)
{
  CALL("ISSatSweeping::sameCandGroup");

  return _candidateGroupIndexes.get(v1, _varCnt+1)==_candidateGroupIndexes.get(v2, _varCnt+2);
}

void ISSatSweeping::addTrueLit(SATLiteral lit)
{
  CALL("ISSatSweeping::addTrueLit");

  ALWAYS(_trueVarSet.insert(lit.var()));
  _trueLits.push(lit);
}

void ISSatSweeping::createCandidates()
{
  CALL("ISSatSweeping::createCandidates");
  ASS_EQ(_solver.getStatus(),SATSolver::SATISFIABLE);
  ASS(_candidateGroups.isEmpty());


  _candidateGroups.push(SATLiteralStack());
  SATLiteralStack& candGrp = _candidateGroups.top();
  Stack<unsigned>::Iterator ivit(_interestingVars);
  while(ivit.hasNext()) {
    unsigned i = ivit.next();
    SATSolver::VarAssignment asgn = _solver.getAssignment(i);
    bool candPolarity;
    switch(asgn) {
    case SATSolver::TRUE:
      candPolarity = true;
      break;
    case SATSolver::FALSE:
      candPolarity = false;
      break;
    case SATSolver::DONT_CARE:
      //don't cares cannot be equivalent to anything, so we just skip it
      continue;
    case SATSolver::NOT_KNOWN: //this is not to be returned with SATISFIABLE solver status
    default:
      ASSERTION_VIOLATION;
    }
    _candidateVarPolarities[i] = candPolarity;
    SATLiteral candLit = SATLiteral(i, candPolarity);
    if(_solver.isZeroImplied(i)) {
      addTrueLit(candLit);
    }
    else {
      candGrp.push(candLit);
      _candidateGroupIndexes.insert(i, 0);
    }
  }

  if(candGrp.size()<2) {
    _candidateGroups.pop();
    ASS(_candidateGroups.isEmpty());
    return;
  }
  _biggestGroupIdx = 0;
}

/**
 * Split the content of orig according to the current assignment. DONT_CARE variables
 * are removed from the group.
 *
 * Ensures that orig will never be smaller than newGrp, and if one of group would
 * become of size 1, it makes it empty.
 */
void ISSatSweeping::splitByCurrAssignment(SATLiteralStack& orig, SATLiteralStack& newGrp)
{
  CALL("ISSatSweeping::splitByCurrAssignment");
  ASS_GE(orig.size(),2);
  ASS_EQ(newGrp.size(),0);
  ASS_EQ(_solver.getStatus(),SATSolver::SATISFIABLE);

  SATLiteralStack::DelIterator oit(orig);
  while(oit.hasNext()) {
    SATLiteral lit = oit.next();
    SATSolver::VarAssignment asgn = _solver.getAssignment(lit.var());
    bool asgnPol;
    switch(asgn) {
    case SATSolver::TRUE:
      asgnPol = true;
      break;
    case SATSolver::FALSE:
      asgnPol = false;
      break;
    case SATSolver::DONT_CARE:
      //don't cares cannot be equivalent to anything, so we just remove it
      oit.del();
      continue;
    case SATSolver::NOT_KNOWN: //this is not to be returned with SATISFIABLE solver status
    default:
      ASSERTION_VIOLATION;
    }
    //true literals remain in orig and false literals go to the newGrp (later the two stacks may be swapped)
    if(asgnPol!=lit.polarity()) {
      oit.del();
      newGrp.push(lit);
    }
  }

  if(newGrp.size()>orig.size()) {
    std::swap(orig,newGrp);
  }
  if(newGrp.size()<2) {
    newGrp.reset();
    if(orig.size()<2) {
      orig.reset();
    }
  }
}

/**
 * Split candidate groups according to the current assignment and put
 * index of the biggest group into @c _biggestGroupIdx.
 */
void ISSatSweeping::splitGroupsByCurrAssignment()
{
  CALL("ISSatSweeping::splitGroupsByCurrAssignment");
  ASS(_candidateGroups.isNonEmpty());

  static SATLiteralStack auxNew;
  ASS(auxNew.isEmpty());

  unsigned biggestSz = 0; //smallest actual group size is 2
  unsigned gi = 0;
  while(gi<_candidateGroups.size()) {
    {//we put this in a special scope as later we might invalidate the currGrp reference
      SATLiteralStack& currGrp = _candidateGroups[gi];

      ASS(auxNew.isEmpty());
      splitByCurrAssignment(currGrp, auxNew);

      ASS_GE(currGrp.size(), auxNew.size());
      if(currGrp.size()>biggestSz) {
	biggestSz = currGrp.size();
	_biggestGroupIdx = gi;
      }
    }

    if(auxNew.isNonEmpty()) {
      unsigned addedGrpIdx = _candidateGroups.size();
      _candidateGroups.push(SATLiteralStack()); //this can reallocate the inside of _candidateGroups
      if(gi+1!=addedGrpIdx) {
	ASS_L(gi+1,addedGrpIdx);
	std::swap(_candidateGroups[gi+1],_candidateGroups[addedGrpIdx]);
      }
      std::swap(_candidateGroups[gi+1],auxNew);
      gi += 2;
    }
    else if(_candidateGroups[gi].isEmpty()) {
      swap(_candidateGroups[gi], _candidateGroups.top());
      _candidateGroups.pop();
    }
    else {
      gi++;
    }
  }

  _candidateGroupIndexes.reset();
  unsigned groupCnt = _candidateGroups.size();
  for(gi=0; gi<groupCnt; gi++) {
    LOG("sat_iss_grps", "Group "<<gi<<" (size "<<_candidateGroups[gi].size()<<")");
    SATLiteralStack::ConstIterator git(_candidateGroups[gi]);
    while(git.hasNext()) {
      SATLiteral lit = git.next();
      LOG("sat_iss_grps_content", "  "<<lit);
      _candidateGroupIndexes.insert(lit.var(), gi);
    }
  }
}

void ISSatSweeping::tryRandomSimulation()
{
  CALL("ISSatSweeping::tryRandomSimulation");
  ASS(!_solver.hasAssumptions());
//  if(_solver.getStatus()!=SATSolver::SATISFIABLE) {
//    _solver.addClauses(SATClauseIterator::getEmpty());
//  }
//  ASS_EQ(_solver.getStatus(), SATSolver::SATISFIABLE);

  SATLiteralStack possiblySatSubset;

  Stack<unsigned> varsInRandomOrder(_interestingVars);

  unsigned vcnt = varsInRandomOrder.size();
  for(unsigned i=0; i<vcnt; i++) {
    unsigned src = Random::getInteger(vcnt-i)+i;
    if(src==i) {
      continue;
    }
    std::swap(varsInRandomOrder[i], varsInRandomOrder[src]);
  }

  Stack<unsigned>::Iterator varIt(varsInRandomOrder);
  while(varIt.hasNext()) {
    unsigned v = varIt.next();
    if(!_candidateGroupIndexes.find(v)) {
      continue;
    }
    bool pol = Random::getBit();
    SATLiteral probeLit = SATLiteral(v, pol);
    _solver.addAssumption(probeLit, true);
    if(_solver.getStatus()==SATSolver::UNSATISFIABLE) {
      _solver.retractAllAssumptions();

      while(possiblySatSubset.size()>1) {
	SATLiteral l = possiblySatSubset.pop();
	_solver.addAssumption(l, true);
      }
      _solver.addAssumption(possiblySatSubset.pop());
      if(_solver.getStatus()==SATSolver::SATISFIABLE) {
	splitGroupsByCurrAssignment();
      }
      _solver.retractAllAssumptions();

      _solver.addAssumption(probeLit);
      if(_solver.getStatus()==SATSolver::UNSATISFIABLE) {
	ASS_NEQ(probeLit.polarity(), _candidateVarPolarities[v]);
	addTrueLit(probeLit.opposite());
	continue;
      }
    }
    possiblySatSubset.push(probeLit);
  }

  _solver.retractAllAssumptions();
}

void ISSatSweeping::addImplication(Impl imp, bool& foundEquivalence)
{
  CALL("ISSatSweeping::addImplication");
  LOG("sat_iss_impl", "discovered implication: "<<imp.first<<" -> "<<imp.second);

  Impl rev = Impl(imp.second, imp.first);

  if(_implications.find(rev)) {
    foundEquivalence = true;
    _equivalentVars.doUnion(imp.first.var(), imp.second.var());
    LOG("sat_iss_impl", "discovered equivalence: "<<imp.first<<" <-> "<<imp.second);
  }
  else {
    _implications.insert(imp);
  }
}

void ISSatSweeping::lookForImplications(SATLiteral probedLit, bool assignedOpposite,
    bool& foundEquivalence)
{
  CALL("ISSatSweeping::lookForImplications");
  ASS_EQ(probedLit.polarity(),_candidateVarPolarities[probedLit.var()]); //only candidate literals can be passed as probedLit
  LOG("sat_iss_impl_scan","looking for implications with "<<probedLit
			<<" assigned as "<<(assignedOpposite ? "opposite" : "normal"));

  Stack<unsigned>::Iterator ivit(_interestingVars);
  while(ivit.hasNext()) {
    unsigned v = ivit.next();
    if(v==probedLit.var()) {
      ASS(_solver.isZeroImplied(v));
      continue;
    }
    if(!_solver.isZeroImplied(v)) {
      continue;
    }
    SATSolver::VarAssignment asgn = _solver.getAssignment(v);
    ASS(asgn==SATSolver::TRUE || asgn==SATSolver::FALSE);
    bool asgnPos = asgn==SATSolver::TRUE;
    SATLiteral candLit = SATLiteral(v, _candidateVarPolarities[v]);
    bool candidateLitTrue = asgnPos==candLit.polarity();
    LOG("sat_iss_impl_scan","have propagation implied: "<<SATLiteral(v,asgnPos)<<" candidate was "<<candLit);
    if(candidateLitTrue==assignedOpposite) {
      //probed lit cannot be equivalent to candidate lit
      //(see documentation to _candidateVarPolarities)
      //We assert the below non-equality because we assume
      //splitGroupsByCurrAssignment() to have been already
      //called on the current assignment.
      ASS_REP2(!sameCandGroup(v,probedLit.var()), v, probedLit.var());
      Impl imp;
      if(assignedOpposite) {
	//~p --> c
	imp = Impl(probedLit.opposite(), candLit);
      }
      else {
	//p --> ~c
	imp = Impl(probedLit, candLit.opposite());
      }
      bool foundEq = false;
      addImplication(imp, foundEq);
      ASS(!foundEq);
      continue;
    }

    Impl imp;
    if(assignedOpposite) {
	//~p --> ~c
	imp = Impl(candLit, probedLit);
    }
    else {
	//p --> ~c
	imp = Impl(probedLit, candLit);
    }
    addImplication(imp, foundEquivalence);
  }
}

bool ISSatSweeping::tryProvingImplication(Impl imp, bool& foundEquivalence)
{
  CALL("ISSatSweeping::tryProvingImplication");

  LOG("sat_iss_try_impl","attempting to prove implication "<<imp.first<<" -> "<<imp.second);
  bool res = tryProvingImplicationInner(imp, foundEquivalence);
  _solver.retractAllAssumptions();
  LOG("sat_iss_try_impl","implication "<<imp.first<<" -> "<<imp.second<<" "<<(res ? "proved" : "disproved"));
  return res;
}

bool ISSatSweeping::tryProvingImplicationInner(Impl imp, bool& foundEquivalence)
{
  CALL("ISSatSweeping::tryProvingImplication");
  ASS(!_solver.hasAssumptions());
  ASS(sameCandGroup(imp.first.var(),imp.second.var()));

  _solver.addAssumption(imp.second.opposite());
  SATSolver::Status status = _solver.getStatus();
  if(status==SATSolver::UNSATISFIABLE) {
    addTrueLit(imp.second);
    foundEquivalence = true;
    return false;
  }

  ASS_EQ(status, SATSolver::SATISFIABLE);
  splitGroupsByCurrAssignment();
  lookForImplications(imp.second, true, foundEquivalence);

  if(foundEquivalence || _solver.trueInAssignment(imp.first)) {
    return false;
  }
  if(_implications.find(imp)) {
    return true;
  }

  _solver.addAssumption(imp.first);
  status = _solver.getStatus();
  if(status==SATSolver::UNSATISFIABLE) {
    LOG("sat_iss_try_impl","assumption of "<<imp.second.opposite()<<" & "<<imp.first<<" unsatisfiable");
    addImplication(imp, foundEquivalence);
    return true;
  }

  splitGroupsByCurrAssignment();
  ASS(!sameCandGroup(imp.first.var(),imp.second.var()));
  return false;

}

/**
 * Run of this function always shrinks the size of the biggest candidate group.
 * Either it discovers an equivalence
 */
void ISSatSweeping::doOneProbing()
{
  CALL("ISSatSweeping::doOneProbing");
  ASS(_candidateGroups.isNonEmpty());

  SATLiteral cand1, cand2;
  {
    SATLiteralStack& currGrp = _candidateGroups[_biggestGroupIdx];
    cand1 = currGrp[0];
    int candRoot = _equivalentVars.root(cand1.var());
    while(currGrp.isNonEmpty()) {
      cand2 = currGrp.top();
      if(candRoot==_equivalentVars.root(cand2.var())) {
	currGrp.pop();
      }
      else {
	break;
      }
    }
    if(currGrp.isEmpty()) {
      if(_biggestGroupIdx!=_candidateGroups.size()-1) {
	std::swap(_candidateGroups[_biggestGroupIdx], _candidateGroups.top());
      }
      else {
	_biggestGroupIdx--;
      }
      ASS(_candidateGroups.top().isEmpty());
      _candidateGroups.pop();
      return;
    }
  }

  bool foundEquivalence = false;
  if(!tryProvingImplication(Impl(cand1, cand2), foundEquivalence) || foundEquivalence) {
    return;
  }

  tryProvingImplication(Impl(cand2, cand1), foundEquivalence);
}

void ISSatSweeping::run()
{
  CALL("ISSatSweeping::run");

  createCandidates();

  tryRandomSimulation();

  while(_candidateGroups.isNonEmpty()) {
    doOneProbing();
  }

  ASS(_equivStack.isEmpty());

  _equivalentVars.evalComponents();
  IntUnionFind::ComponentIterator cit(_equivalentVars);
  while(cit.hasNext()) {
    IntUnionFind::ElementIterator eit(cit.next());
    ALWAYS(eit.hasNext());
    unsigned v1 = eit.next();
    if(v1==0) {
      //this is not an actual variable, just an artifact of
      //SAT variables being 1-based while IntUnionFind 0-based
      ASS(!eit.hasNext());
      continue;
    }
    SATLiteral lit1(v1, _candidateVarPolarities[v1]);
    while(eit.hasNext()) {
      unsigned v2 = eit.next();
      SATLiteral lit2(v2, _candidateVarPolarities[v2]);
      _equivStack.push(Equiv(lit1, lit2));
    }
  }
}

//void ISSatSweeping::doOneLitProbing(SATLiteral lit)
//{
//  CALL("ISSatSweeping::doOneLitProbing");
//  ASS(!_solver.hasAssumptions());
//
//  bool foundEquiv = false;
//  _solver.addAssumption(lit.opposite());
//  SATSolver::Status status = _solver.getStatus();
//  if(status==SATSolver::UNSATISFIABLE) {
//    addTrueLit(lit);
//  }
//  else {
//    ASS_EQ(status, SATSolver::SATISFIABLE);
//    splitGroupsByCurrAssignment();
//    lookForImplications(lit, true, foundEquiv);
//  }
//  _solver.retractAllAssumptions();
//
//  if(foundEquiv || status==SATSolver::UNSATISFIABLE) {
//    return;
//  }
//
//  _solver.addAssumption(lit);
//  status = _solver.getStatus();
//  ASS_EQ(status, SATSolver::SATISFIABLE);
//  splitGroupsByCurrAssignment();
//  lookForImplications(lit, false, foundEquiv);
//  _solver.retractAllAssumptions();
//
//}



}
