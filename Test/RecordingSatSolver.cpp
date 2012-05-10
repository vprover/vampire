/**
 * @file RecordingSatSolver.cpp
 * Implements class RecordingSatSolver.
 */

#include <sstream>

#include "Lib/Int.hpp"
#include "Lib/List.hpp"

#include "SAT/SATClause.hpp"

#include "RecordingSatSolver.hpp"

namespace Test
{

#define REC(x) LOG("sat_recorder",getHdr()<<x)

/**
 * Return header to be used for log outputs of this solver
 */
string RecordingSatSolver::getHdr() const
{
  CALL("RecordingSatSolver::getHdr");

  return "sat_"+Int::toHexString(reinterpret_cast<size_t>(this))+" ";
}

void RecordingSatSolver::addClauses(SATClauseIterator cit0, bool onlyPropagate)
{
  CALL("RecordingSatSolver::addClauses");

  SATClauseList* clauses = 0;
  SATClauseList::pushFromIterator(cit0, clauses);
  clauses = clauses->reverse();

  stringstream clausesStm;
  SATClauseList::Iterator cit(clauses);
  while(cit.hasNext()) {
    SATClause* cl = cit.next();
    clausesStm << cl->toDIMACSString();
    if(cit.hasNext()) {
      clausesStm << "|";
    }
  }

  REC("act=ac:op="<<onlyPropagate<<":clauses="<<clausesStm);

  _inner->addClauses(pvi(SATClauseList::DestructiveIterator(clauses)), onlyPropagate);
}

void RecordingSatSolver::randomizeAssignment()
{
  CALL("RecordingSatSolver::randomizeAssignment");

  REC("act=ra");

  _inner->randomizeAssignment();
}

void RecordingSatSolver::ensureVarCnt(unsigned newVarCnt)
{
  CALL("RecordingSatSolver::ensureVarCnt");

  REC("act=evc:nwc="<<newVarCnt);

  _inner->ensureVarCnt(newVarCnt);
}

void RecordingSatSolver::addAssumption(SATLiteral lit, unsigned conflictCountLimit)
{
  CALL("RecordingSatSolver::addAssumption");

  REC("act=aa:litVar="<<lit.var()<<":litPol="<<lit.polarity()<<":ccl="<<conflictCountLimit);

  _inner->addAssumption(lit, conflictCountLimit);
}

void RecordingSatSolver::retractAllAssumptions()
{
  CALL("RecordingSatSolver::retractAllAssumptions");

  REC("act=raa");

  _inner->retractAllAssumptions();
}


}
