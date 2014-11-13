/**
 * @file MinimizingSolver.cpp
 * Implements class MinimizingSolver.
 */

#include "SAT/SATClause.hpp"

#include "MinimizingSolver.hpp"

namespace SAT
{

MinimizingSolver::MinimizingSolver(SATSolver* inner,bool splitclausesonly)
 : _varCnt(0), _inner(inner), _splitclausesonly(splitclausesonly),
   _assignmentValid(false)
{
  CALL("MinimizingSolver::MinimizingSolver");

}

void MinimizingSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("MinimizingSolver::ensureVarCnt");

  _varCnt = std::max(_varCnt, newVarCnt);
  _inner->ensureVarCnt(newVarCnt);
  _asgn.expand(newVarCnt);
  _watcher.expand(newVarCnt);

  unsigned vc2 = newVarCnt*2;
  _unsClCnt.expand(vc2, 0);
  _clIdx.expand(vc2);
  _assignmentValid = false;
}

bool MinimizingSolver::isNonEmptyClause(SATClause* cl)
{
  return cl->length()!=0;
}

void MinimizingSolver::addClauses(SATClauseIterator cit, bool onlyPropagate,bool useInPartialModel)
{
  CALL("MinimizingSolver::addClauses");

  static SATClauseStack newClauses;
  newClauses.reset();
  newClauses.loadFromIterator(cit);

  // We only need to keep track of these clauses if they need to be covered by the partial model
  // This is safe as the model produced is always a 'sub-model' of that produced by inner
  // and not adding clauses to _unprocessed should only result in more variables being marked
  // as DONT_CARE (if they only appear in clauses not to be used in the partial model)
  // - Giles
  if(useInPartialModel || ! _splitclausesonly ) {
    //we need to filter out the empty clause -- it won't have any influence on our algorithm
    //(as it will make the problem unsat and we process only satisfiale assignment), but it
    //is a corner case that needs to be handled
    _unprocessed.loadFromIterator(
        getFilteredIterator(SATClauseStack::BottomFirstIterator(newClauses), isNonEmptyClause));
  }

  _inner->addClauses(pvi(SATClauseStack::BottomFirstIterator(newClauses)), onlyPropagate,useInPartialModel);
  _assignmentValid = false;
}

SATSolver::VarAssignment MinimizingSolver::getAssignment(unsigned var)
{
  CALL("MinimizingSolver::getAssignment");
  ASS_EQ(_inner->getStatus(), SATISFIABLE);

  if(!_assignmentValid) {
    updateAssignment();
  }

  if(!_assumptions.isEmpty() && _assumptions.find(var)) {
    return _assumptions.get(var) ? SATSolver::TRUE : SATSolver::FALSE;
  }

  if(_watcher[var].isEmpty()) {
    return SATSolver::DONT_CARE;
  }
  return _asgn[var] ? SATSolver::TRUE : SATSolver::FALSE;
}

bool MinimizingSolver::isZeroImplied(unsigned var)
{
  CALL("MinimizingSolver::isZeroImplied");
  bool res = _inner->isZeroImplied(var);
  ASS(!res || getAssignment(var)!=DONT_CARE); //zero-implied variables cannot become a don't care
  return res;
}

/**
 * Return a true SATLiteral that will satisfy the most unsatisfied
 * clauses, or SATLiteral::dummy() if there isn't any literal that
 * satisfies unsatisfied clauses.
 */
SATLiteral MinimizingSolver::getMostSatisfyingTrueLiteral()
{
  CALL("MinimizingSolver::getMostSatisfyingTrueLiteral");

  //TODO:use a heap for this
  // Giles: Definitely use a heap! This is iterating over all literals
  // in the SAT solver on each call, and will be called many times
  unsigned best=0;
  SATLiteral bestLit = SATLiteral::dummy();

  unsigned ctrSz = _varCnt*2;
  for(unsigned i=0; i<ctrSz; i++) {
    SATLiteral lit(i);
    if(_asgn[lit.var()]!=lit.polarity()) {
      continue;
    }
    if(_unsClCnt[i]>best) {
      best = _unsClCnt[i];
      bestLit = lit;
    }
  }
  return bestLit;
}

/**
 * Add a literal into the resulting assignment
 */
void MinimizingSolver::selectLiteral(SATLiteral lit)
{
  CALL("MinimizingSolver::selectLiteral");
  ASS_EQ(lit.polarity(), _asgn[lit.var()]); //literal is true in the inner assignment

  unsigned var = lit.var();

  SATClauseStack& satisfied = _clIdx[lit.content()];
  SATClauseStack& watch = _watcher[var];
  while(satisfied.isNonEmpty()) {
    SATClause* cl = satisfied.pop();
    if(!_satisfiedClauses.insert(cl)) {
      continue;
    }
    watch.push(cl);
    SATClause::Iterator cit(*cl);
    while(cit.hasNext()) {
      SATLiteral lit = cit.next();
      ASS_G(_unsClCnt[lit.content()], 0);
      _unsClCnt[lit.content()]--;
    }
  }
}

void MinimizingSolver::putIntoIndex(SATClause* cl)
{
  CALL("MinimizingSolver::putIntoIndex");

  SATClause::Iterator cit(*cl);
  while(cit.hasNext()) {
    SATLiteral lit = cit.next();

    unsigned i = lit.content();
    _clIdx[i].push(cl);
    _unsClCnt[i]++;
  }
}

bool MinimizingSolver::tryPuttingToAnExistingWatch(SATClause* cl)
{
  CALL("MinimizingSolver::tryPuttingToAnExistingWatch");

  SATClause::Iterator cit(*cl);
  while(cit.hasNext()) {
    SATLiteral lit = cit.next();
    unsigned var = lit.var();
    if(_asgn[var]==lit.polarity() && _watcher[var].isNonEmpty()) {
      ALWAYS(_satisfiedClauses.insert(cl));
      _watcher[var].push(cl);
      return true;
    }
  }
  return false;
}

/**
 * Move satisfied unprocessed clauses into an appropriate watch, and
 * unsatisfied unprocessed clauses into _clIdx
 */
void MinimizingSolver::processUnprocessed()
{
  CALL("MinimizingSolver::processUnprocessed");

  while(_unprocessed.isNonEmpty()) {
    SATClause* cl = _unprocessed.pop();
    ASS_G(cl->length(),0)
    if(!tryPuttingToAnExistingWatch(cl)) {
      putIntoIndex(cl);
    }
  }
}

/**
 * Update the values in _asgn and move the clauses whose watch
 * became unsatisfied to _unprocessed.
 */
void MinimizingSolver::processInnerAssignmentChanges()
{
  CALL("MinimizingSolver::processInnerAssignmentChanges");

  for(unsigned v=1; v<_varCnt; v++) {
    VarAssignment va = _inner->getAssignment(v);
    bool changed;
    switch(va) {
    case DONT_CARE:
      changed = false;
      break;
    case TRUE:
      changed = !_asgn[v];
      _asgn[v] = true;
      break;
    case FALSE:
      changed = _asgn[v];
      _asgn[v] = false;
      break;
    case NOT_KNOWN:
    default:
      ASSERTION_VIOLATION;
      break;
    }

    if(changed) {
      SATClauseStack& watch = _watcher[v];
      _unprocessed.loadFromIterator(SATClauseStack::Iterator(watch));
      _satisfiedClauses.removeIteratorElements(SATClauseStack::Iterator(watch));
      watch.reset();
    }
  }
}

void MinimizingSolver::updateAssignment()
{
  CALL("MinimizingSolver::updateAssignment");

  TimeCounter tca(TC_MINIMIZING_SOLVER);
  
  processInnerAssignmentChanges();
  processUnprocessed();

  for(;;) {
    SATLiteral lit = getMostSatisfyingTrueLiteral();
    if(lit==SATLiteral::dummy()) {
      break;
    }
    selectLiteral(lit);
  }

  _assignmentValid = true;
}


void MinimizingSolver::addAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("MinimizingSolver::addAssumption");

  _assumptions.insert(lit.var(), lit.polarity());
  _assignmentValid = false;
  _inner->addAssumption(lit, conflictCountLimit);
}

void MinimizingSolver::retractAllAssumptions()
{
  CALL("MinimizingSolver::retractAllAssumptions");

  _assumptions.reset();
  _inner->retractAllAssumptions();
}


}
