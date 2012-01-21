
#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ScopedPtr.hpp"

#include "SAT/TransparentSolver.hpp"
#include "SAT/TWLSolver.hpp"

#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"

#define UNIT_ID transpSolver
UT_CREATE;

using namespace std;
using namespace Lib;
using namespace SAT;
using namespace Test;



TEST_FUN(transpSolver1)
{
  SATSolverSCP solver(new TransparentSolver(new TWLSolver(*env.options, false)));

  solver->ensureVarCnt(3);
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(2,1,2) )), false);
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addAssumption(SATLiteral(2,false));
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addAssumption(SATLiteral(1,false));
  ASS_EQ(solver->getStatus(),SATSolver::UNSATISFIABLE);
  solver->retractAllAssumptions();
  ASS_NEQ(solver->getStatus(),SATSolver::UNSATISFIABLE);

  solver->ensureVarCnt(7);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(2,3,4) )), false);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(2,3,5) )), false);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(2,-5,6) )), false);
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addAssumption(SATLiteral(3,false));
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addAssumption(SATLiteral(6,false));
  ASS_EQ(solver->getStatus(),SATSolver::UNSATISFIABLE);
  solver->retractAllAssumptions();
  ASS_NEQ(solver->getStatus(),SATSolver::UNSATISFIABLE);

  solver->ensureVarCnt(12);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(2,10,11) )), false);
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(1,-10) )), false);
  ASS_EQ(solver->getStatus(),SATSolver::SATISFIABLE);
  solver->addClauses(pvi(getSingletonIterator( TestUtils::buildSATClause(1,-11) )), false);
  ASS_EQ(solver->getStatus(),SATSolver::UNSATISFIABLE);
}

