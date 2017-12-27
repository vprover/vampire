
/*
 * File ISSatSweeping.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file ISSatSweeping.cpp
 * Implements class ISSatSweeping.
 */


#include "Lib/Random.hpp"

#include "ISSatSweeping.hpp"

namespace SAT
{

/**
 * @param varCnt is the count of SAT variables and thus also the index of the maximal one (variable 0 unused)
 * @param solver SATSolver object whose state should we sweep for literal
 * 	equivalences. This solver should be in a satisfiable state without
 * 	any assumptions. We will add assumptions to probe for equivalences
 * 	and then retract them in the end.
 * @param interestingVarIterator iterator on variables that are to be
 * 	examined for equivalences. Each variable can appear at most once.
 * @param doRandomSimulation ???
 * @param conflictLimit ???
 * @param collectImplications ???
 */
ISSatSweeping::ISSatSweeping(unsigned varCnt, SATSolverWithAssumptions& solver, IntIterator interestingVarIterator,
			     bool doRandomSimulation, unsigned conflictLimit, bool collectImplications)
: _doRandomSimulation(doRandomSimulation),
  _conflictUpperLimit(conflictLimit),
  _collectImplications(collectImplications),
  _varCnt(varCnt),
  _interestingVarsSet(varCnt+1),
  _probingGroupIndex(0),
  _probingElementIndex(0),
  _conflictCountLimit(0),
  _reachedUpperConflictLimit(false),
  _candidateVarPolarities(varCnt+1),
  _candidateGroupIndexes(varCnt+1),
  _equivalentVars(varCnt+1),
  _lastSweepingImplicationCnt(0),
  _solver(solver)
{
  CALL("ISSatSweeping::ISSatSweeping");

  // ASS_EQ(solver.getStatus(),SATSolver::SATISFIABLE);
  ASS(!solver.hasAssumptions());

  if(interestingVarIterator.isInvalid()) {
    interestingVarIterator = pvi(getRangeIterator(1,static_cast<int>(varCnt+1)));
  }

  _interestingVars.loadFromIterator(interestingVarIterator);
  _interestingVarsSet.insertFromIterator(Stack<unsigned>::Iterator(_interestingVars));

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
  // ASS_EQ(_solver.getStatus(),SATSolver::SATISFIABLE);
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
    _unfinishedAmount = 0;
  }
  else {
    _unfinishedAmount = candGrp.size()-1;
  }
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
  // ASS_EQ(_solver.getStatus(),SATSolver::SATISFIABLE);

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

  unsigned gi = 0;
  while(gi<_candidateGroups.size()) {
    {//we put this in a special scope as later we might invalidate the currGrp reference
      SATLiteralStack& currGrp = _candidateGroups[gi];

      ASS(auxNew.isEmpty());
      splitByCurrAssignment(currGrp, auxNew);
      ASS_GE(currGrp.size(), auxNew.size());
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

  _unfinishedAmount = 0;
  _candidateGroupIndexes.reset();
  unsigned groupCnt = _candidateGroups.size();
  for(gi=0; gi<groupCnt; gi++) {
    SATLiteralStack& grp = _candidateGroups[gi];
    ASS_GE(grp.size(),2);
    _unfinishedAmount += grp.size()-1;
    SATLiteralStack::ConstIterator git(grp);
    while(git.hasNext()) {
      SATLiteral lit = git.next();
      _candidateGroupIndexes.insert(lit.var(), gi);
    }
  }
}

void ISSatSweeping::tryRandomSimulation()
{
  CALL("ISSatSweeping::tryRandomSimulation");
  ASS(!_solver.hasAssumptions());

  if(_candidateGroups.isEmpty()) {
    return;
  }

  // TODO: this may be here just to make sure that the solver's internal status
  // in not UNKNOWN, which would violate assertion in randomizeAssignment


  unsigned initLives = 3;
  unsigned lives = initLives;

  do {
    unsigned oldUnfinished = _unfinishedAmount;

    _solver.randomizeForNextAssignment(_varCnt);
    ALWAYS(_solver.solve() == SATSolver::SATISFIABLE);

    splitGroupsByCurrAssignment();

    if(oldUnfinished==_unfinishedAmount) {
      lives--;
    }
    else {
      lives = initLives;
    }
  } while(_unfinishedAmount && lives>0);
}

void ISSatSweeping::addImplication(Impl imp, bool& foundEquivalence)
{
  CALL("ISSatSweeping::addImplication");

  Impl rev = Impl(imp.second, imp.first);

  if(_implications.find(rev)) {
    foundEquivalence = _equivalentVars.doUnion(imp.first.var(), imp.second.var());
    _implications.remove(rev);
    onRedundantImplicationDiscovered();
  }
  else {
    _implications.insert(imp);
  }
}

void ISSatSweeping::onRedundantImplicationDiscovered()
{
  CALL("ISSatSweeping::onRedundantImplicationDiscovered");

  if(_implications.size()>1000 && _implications.size()>_lastSweepingImplicationCnt*2) {
    doRedundantImplicationSweeping();
    _lastSweepingImplicationCnt = _implications.size();
  }
}

void ISSatSweeping::doRedundantImplicationSweeping()
{
  CALL("ISSatSweeping::doRedundantImplicationSweeping");

  size_t removedCnt = 0;
  DHSet<Impl>::DelIterator implIt(_implications);
  while(implIt.hasNext()) {
    Impl imp = implIt.next();
    unsigned v1 = imp.first.var();
    unsigned v2 = imp.second.var();
    if(_equivalentVars.root(v1)!=_equivalentVars.root(v2)) {
      //implication is not implied by equivalences

      //if variables are in different candidate groups, we can throw them out, unless
      //we are interested in collecting all implications
      if(_collectImplications || sameCandGroup(v1,v2)) {
	continue;
      }
    }
    implIt.del();
    removedCnt++;
  }
}

void ISSatSweeping::lookForImplications(SATLiteral probedLit, bool assignedOpposite,
    bool& foundEquivalence)
{
  CALL("ISSatSweeping::lookForImplications");
  ASS_EQ(probedLit.polarity(),_candidateVarPolarities[probedLit.var()]); //only candidate literals can be passed as probedLit

  unsigned probedVar = probedLit.var();

  static SATLiteralStack ziStack;
  ziStack.reset();

  _solver.collectZeroImplied(ziStack);

  SATLiteralStack::Iterator ziit(ziStack);
  while(ziit.hasNext()) {
    SATLiteral lit = ziit.next();
    unsigned litVar = lit.var();

    ASS(_solver.isZeroImplied(litVar));
    // ASS(_solver.getStatus()==SATSolver::UNKNOWN || _solver.trueInAssignment(lit));

    if(!_interestingVarsSet.find(litVar)) {
      continue;
    }
    if(!_collectImplications && !sameCandGroup(litVar,probedVar)) {
      continue;
    }
    if(litVar==probedVar) {
      ASS_EQ(lit.polarity(),probedLit.polarity()^assignedOpposite);
      continue;
    }
    SATLiteral candLit = SATLiteral(litVar, _candidateVarPolarities[litVar]);
    bool candidateLitTrue = lit==candLit;
    if(candidateLitTrue==assignedOpposite) {
      //probed lit cannot be equivalent to candidate lit
      //(see documentation to _candidateVarPolarities)
      //We assert the below non-equality because we assume
      //splitGroupsByCurrAssignment() to have been already
      //called on the current assignment.      
      //ASS_REP2(_solver.getStatus()==SATSolver::UNKNOWN || !sameCandGroup(litVar,probedVar), lit, probedLit);
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
    else {
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
}

bool ISSatSweeping::tryProvingImplication(Impl imp, bool& foundEquivalence)
{
  CALL("ISSatSweeping::tryProvingImplication");

  if(_implications.find(imp)) {
    return true;
  }
  bool res = tryProvingImplicationInner(imp, foundEquivalence);
  _solver.retractAllAssumptions();
  return res;
}

/**
 * Try proving implication imp (f -> s) by asserting ~s and afterward f.
 * If ~s itself is unsatisfiable, we've proven that s has to be true. We
 * also examine the intermediate assignment and literals implied by
 * unit-propagation of the ~s. If we find to s be equivalent to something else,
 * we terminate early and set foundEquivalence to true.
 *
 * This is a inner function for @c tryProvingImplication, the outer function will
 * retract assumptions made by this one.
 */
bool ISSatSweeping::tryProvingImplicationInner(Impl imp, bool& foundEquivalence)
{
  CALL("ISSatSweeping::tryProvingImplication");
  ASS(!_solver.hasAssumptions());
  ASS(sameCandGroup(imp.first.var(),imp.second.var()));

  _solver.addAssumption(imp.second.opposite());
  SATSolver::Status status = _solver.solve(_conflictCountLimit);
  if(status==SATSolver::UNSATISFIABLE) {
    addTrueLit(imp.second);
    foundEquivalence = true;
    return false;
  }

  if(status==SATSolver::SATISFIABLE) {
    splitGroupsByCurrAssignment();
  }
  lookForImplications(imp.second, true, foundEquivalence);

  if(foundEquivalence) {
    return false;
  }
  if(_implications.find(imp)) {
    return true;
  }

  if(status==SATSolver::SATISFIABLE && _solver.trueInAssignment(imp.first)) {
    //if SATISFIABLE, we did splitGroupsByCurrAssignment() with this assignment, so
    //the two elements of the implication must have ended in different groups
    ASS(!sameCandGroup(imp.first.var(),imp.second.var()));
    return false;
  }

  _solver.addAssumption(imp.first);
  status = _solver.solve(_conflictCountLimit);
  if(status==SATSolver::UNSATISFIABLE) {
    addImplication(imp, foundEquivalence);
    return true;
  }

  if(status==SATSolver::SATISFIABLE) {
    splitGroupsByCurrAssignment();
    ASS(!sameCandGroup(imp.first.var(),imp.second.var()));
  }
  return false;
}

/**
 * Run of this function always shrinks the size of the biggest candidate group.
 * Either it discovers an equivalence
 */
bool ISSatSweeping::doOneProbing()
{
  CALL("ISSatSweeping::doOneProbing");

  SATLiteral cand1, cand2;
  if(!getProbingCandidates(cand1, cand2)) {
    return false;
  }
  ASS_NEQ(_equivalentVars.root(cand1.var()), _equivalentVars.root(cand2.var()));

  bool foundEquivalence = false;
  if(tryProvingImplication(Impl(cand1, cand2), foundEquivalence) && !foundEquivalence) {
    tryProvingImplication(Impl(cand2, cand1), foundEquivalence);
  }
  return true;
}

bool ISSatSweeping::getProbingCandidates(SATLiteral& cand1, SATLiteral& cand2)
{
  CALL("ISSatSweeping::getProbingCandidates");

  if(getProbingCandidatesWithinRotation(cand1, cand2)) {
    return true;
  }
  if(!nextRotation()) {
    return false;
  }
  if(!getProbingCandidatesWithinRotation(cand1, cand2)) {
    //we eliminated all potential candidates, so it should
    //not be possible to get to the next rotation
    ASS(!nextRotation());
    return false;
  }
  return true;
}

bool ISSatSweeping::nextRotation()
{
  CALL("ISSatSweeping::nextRotation");

  if(_candidateGroups.isEmpty()) {
    return false;
  }
  _probingGroupIndex = 0;
  _probingElementIndex = 0;

  if(_conflictCountLimit) {
    if(_conflictCountLimit<UINT_MAX/2) {
      _conflictCountLimit*=2;
    }
    else {
      _conflictCountLimit=UINT_MAX;
    }
  }
  else {
    _conflictCountLimit++;
  }
  if(_conflictCountLimit>_conflictUpperLimit) {
    _reachedUpperConflictLimit = true;
  }
  return true;
}


/**
 * Select probing candidates from group grp, not considering elements on positions less than
 * @c firstIndex for the first candidate (they may be considered for the second candidate though).
 * Do a feasibility check on candidates, so that we don't select a candidate that is known to be
 * always true, or candidates that are already known to be equivalent. The unfeasible candidates are
 * also removed from @c grp.
 */
bool ISSatSweeping::getProbingCandidatesFromGroup(SATLiteralStack& grp, unsigned firstIndex,
    SATLiteral& cand1, SATLiteral& cand2)
{
  CALL("ISSatSweeping::getProbingCandidatesFromGroup");
  ASS_G(grp.size(),1);

  if(firstIndex>=grp.size()) {
    return false;
  }

  while(_trueLits.find(grp[firstIndex])) {
    if(firstIndex<grp.size()-1) {
      grp[firstIndex] = grp.pop();
    }
    else {
      ASS_EQ(firstIndex,grp.size()-1);
      grp.pop();
      if(grp.size()==1) {
	//we empty groups of size 1
	grp.pop();
      }
      return false;
    }
  }
  ASS_GE(grp.size(),2);

  SATLiteral c1 = grp[firstIndex];
  int c1Root = _equivalentVars.root(c1.var());

  //Now we try to find the second candidate. We try the next element
  //in the group (ruling out unfeasible candidates that are in the
  //same equivalence class or are shown to be true). When there is no
  //next element, we make the first candidate to be the first element
  //in the group (grp[0]) and start looking for the second candidate again, this
  //time at the position grp[1].

  unsigned secondIndex = firstIndex+1;
  if(secondIndex>=grp.size()) {
    ASS_EQ(c1,grp.top());
    swap(grp[0], grp.top());
    firstIndex = 0;
    secondIndex = 1;
  }
  while(_trueLits.find(grp[secondIndex]) || _equivalentVars.root(grp[secondIndex].var())==c1Root) {
    if(secondIndex<grp.size()-1) {
      grp[secondIndex] = grp.pop();
    }
    else {
      ASS_EQ(secondIndex,grp.size()-1);
      grp.pop();
      ASS(!grp.isEmpty());
      if(grp.size()==1) {
	grp.pop();
	return false;
      }
      //At this point c1 is the last in this group, so we know
      //we won't be going into this group again in this rotation.
      //We put the first element in the beginning and on the second
      //element we'll hope to get the cand2
      ASS_EQ(c1,grp.top());
      swap(grp[0], grp.top());
      firstIndex = 0;
      secondIndex = 1;
    }
  }

  cand1 = c1;
  cand2 = grp[secondIndex];
  ASS_NEQ(cand1,cand2);
  ASS_NEQ(_equivalentVars.root(cand1.var()),_equivalentVars.root(cand2.var()));
  ASS(!_trueLits.find(cand1));
  ASS(!_trueLits.find(cand2));
  ASS(grp.find(cand1));
  ASS(grp.find(cand2));
  return true;
}

bool ISSatSweeping::getProbingCandidatesWithinRotation(SATLiteral& cand1, SATLiteral& cand2)
{
  CALL("ISSatSweeping::getProbingCandidates");

  cand1 = SATLiteral::dummy();

  for(;;) {
    if(_probingGroupIndex>=_candidateGroups.size()) {
      return false;
    }

    SATLiteralStack& currGrp = _candidateGroups[_probingGroupIndex];
    bool found = getProbingCandidatesFromGroup(currGrp, _probingElementIndex, cand1, cand2);
    ASS_NEQ(currGrp.size(), 1); //group is either empty or of size at least two
    if(found) {
      _probingElementIndex++;
      return true;
    }
    _probingElementIndex = 0;
    if(currGrp.isEmpty()) {
      if(_probingGroupIndex!=_candidateGroups.size()-1) {
	ASS_L(_probingGroupIndex,_candidateGroups.size()-1);
	swap(currGrp, _candidateGroups.top());
      }
      _candidateGroups.pop();
    }
    else {
      _probingGroupIndex++;
    }
  }
}

void ISSatSweeping::run()
{
  CALL("ISSatSweeping::run");

  createCandidates();

  if(_doRandomSimulation) {
    tryRandomSimulation();
  }

  //do the actual proving

  while(!_reachedUpperConflictLimit && doOneProbing()) { }

  //and now extract the results

  ASS(_reachedUpperConflictLimit || _candidateGroups.isEmpty());

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
    unsigned compSz = 1;
    SATLiteral lit1(v1, _candidateVarPolarities[v1]);
    while(eit.hasNext()) {
      unsigned v2 = eit.next();
      SATLiteral lit2(v2, _candidateVarPolarities[v2]);
      _equivStack.push(Equiv(lit1, lit2));
      compSz++;
    }
  }
}




}
