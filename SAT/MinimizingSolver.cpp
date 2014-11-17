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
   _assignmentValid(false), _heap(CntComparator(_unsClCnt))
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
  _unsClCnt.expand(newVarCnt, 0);
  _heap.elMap().expand(newVarCnt);
  _clIdx.expand(newVarCnt);
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

  if(admitsDontcare(var)) {
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
 * Give a concrete value (as opposed to don't-care) to the given variable.
 */
void MinimizingSolver::selectVariable(unsigned var)
{
  CALL("MinimizingSolver::selectVariable");  
  ASS_G(_unsClCnt[var],0);
  
  SATClauseStack& satisfied = _clIdx[var];
  SATClauseStack& watch = _watcher[var];
  while(satisfied.isNonEmpty()) {
    SATClause* cl = satisfied.pop();
    if(!_satisfiedClauses.insert(cl)) {
      continue;
    }
    watch.push(cl);
    SATClause::Iterator cit(*cl);
    while(cit.hasNext()) {
      SATLiteral cl_lit = cit.next();
      unsigned cl_var = cl_lit.var(); 
      if (cl_lit.polarity() == _asgn[cl_var]) {
        ASS_G(_unsClCnt[cl_var], 0);
        _unsClCnt[cl_var]--;
        if (cl_var != var) { // var has been just popped
          _heap.notifyIncrease(cl_var); //It was an increase wrt max-heap
        }
      }
    }
  }  
}

void MinimizingSolver::putIntoIndex(SATClause* cl)
{
  CALL("MinimizingSolver::putIntoIndex");

  SATClause::Iterator cit(*cl);
  while(cit.hasNext()) {
    SATLiteral lit = cit.next();
    unsigned var = lit.var();

    if (lit.polarity() == _asgn[var]) {
      _clIdx[var].push(cl);
      _unsClCnt[var]++;
    }
  }
}

bool MinimizingSolver::tryPuttingToAnExistingWatch(SATClause* cl)
{
  CALL("MinimizingSolver::tryPuttingToAnExistingWatch");

  SATClause::Iterator cit(*cl);
  while(cit.hasNext()) {
    SATLiteral lit = cit.next();
    unsigned var = lit.var();
    if(_asgn[var]==lit.polarity() && !admitsDontcare(var)) {
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
void MinimizingSolver::processUnprocessedAndFillHeap()
{
  CALL("MinimizingSolver::processUnprocessed");

  while(_unprocessed.isNonEmpty()) {
    SATClause* cl = _unprocessed.pop();
    ASS_G(cl->length(),0)
    if(!tryPuttingToAnExistingWatch(cl)) {
      putIntoIndex(cl);
    }
  }
  
  for(unsigned var=0; var<_varCnt; var++) {
    ASS(!_heap.contains(var));
    if(_unsClCnt[var]>0) {            
      _heap.addToEnd(var);      
    }
  }
  _heap.heapify();    
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
  processUnprocessedAndFillHeap();

  while (!_heap.isEmpty()) {
    unsigned best_var = _heap.pop();
    if (_unsClCnt[best_var] > 0) {
      selectVariable(best_var);
      ASS_EQ(_unsClCnt[best_var],0);
      ASS(_clIdx[best_var].isEmpty());
    } else {
      _clIdx[best_var].reset();
    }
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
