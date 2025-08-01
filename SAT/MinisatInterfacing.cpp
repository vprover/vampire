/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file MinisatInterfacing.cpp
 * Implements class MinisatInterfacing
 */

#include "MinisatInterfacing.hpp"

#include "Lib/DArray.hpp"

namespace SAT
{

using namespace Shell;
using namespace Lib;

using namespace Minisat;

/**
 * Make the solver handle clauses with variables up to @b newVarCnt
 * (but see vampireVar2Minisat!)
 */
void MinisatInterfacing::ensureVarCount(unsigned newVarCnt)
{
  while(_solver.nVars() < (int)newVarCnt) {
    _solver.newVar();
  }
}

unsigned MinisatInterfacing::newVar() 
{
  return minisatVar2Vampire(_solver.newVar());
}

Status MinisatInterfacing::solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit)
{
  // load assumptions:
  _assumptions.clear();
  SATLiteralStack::ConstIterator it(assumps);
  while (it.hasNext()) {
    _assumptions.push(vampireLit2Minisat(it.next()));
  }

  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

SATLiteralStack MinisatInterfacing::failedAssumptions() {
  ASS_EQ(_status, Status::UNSATISFIABLE)

  SATLiteralStack result;
  for (int i = 0; i < _solver.conflict.size(); i++)
    result.push(minisatLit2Vampire(_solver.conflict[i]).opposite());
  return result;
}

/**
 * Solve modulo assumptions and set status.
 * @b conflictCountLimit as with addAssumption.
 */
void MinisatInterfacing::solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit)
{
  // TODO: consider calling simplify(); or only from time to time?

  _solver.setConfBudget(conflictCountLimit); // treating UINT_MAX as \infty
  lbool res = _solver.solveLimited(_assumptions);

  if (res == l_True) {
    _status = Status::SATISFIABLE;
  } else if (res == l_False) {
    _status = Status::UNSATISFIABLE;
  } else {
    _status = Status::UNKNOWN;
  }
}

/**
 * Add clause into the solver.
 *
 */
void MinisatInterfacing::addClause(SATClause* cl)
{
  // store to later generate the refutation
  PrimitiveProofRecordingSATSolver::addClause(cl);

  // TODO: consider measuring time
  static vec<Lit> mcl;
  mcl.clear();

  unsigned clen=cl->length();
  for(unsigned i=0;i<clen;i++) {
    SATLiteral l = (*cl)[i];
    mcl.push(vampireLit2Minisat(l));
  }

  _solver.addClause(mcl);
}

/**
 * Perform solving and return status.
 */
Status MinisatInterfacing::solveLimited(unsigned conflictCountLimit)
{
  _assumptions.clear();
  solveModuloAssumptionsAndSetStatus(conflictCountLimit);
  return _status;
}

VarAssignment MinisatInterfacing::getAssignment(unsigned var)
{
	ASS_EQ(_status, Status::SATISFIABLE);
	ASS_G(var,0); ASS_LE(var,(unsigned)_solver.nVars());
  lbool res;

  Minisat::Var mvar = vampireVar2Minisat(var);
  if (mvar < _solver.model.size()) {
    if ((res = _solver.modelValue(mvar)) == l_True) {
      return VarAssignment::TRUE;
    } else if (res == l_False) {
      return VarAssignment::FALSE;
    } else {
      ASSERTION_VIOLATION;
      return VarAssignment::NOT_KNOWN;
    }
  } else { // new vars have been added but the model didn't grow yet
    return VarAssignment::DONT_CARE;
  }
}

bool MinisatInterfacing::isZeroImplied(unsigned var)
{
  ASS_G(var,0); ASS_LE(var,(unsigned)_solver.nVars());
  
  /* between calls to _solver.solve*
   value is undefined for all accept zero implied variables */
  return _solver.value(vampireVar2Minisat(var)) != l_Undef;
}

SATClauseList* MinisatInterfacing::minimizePremiseList(SATClauseList* premises, SATLiteralStack& assumps)
{
  Minisat::Solver solver;

  static DHMap<int,SATClause*> var2prem;
  var2prem.reset();

  static vec<Lit> ass; // assumptions for the final call
  ass.clear();

  int cl_no = 0;

  SATClauseList* it= premises;
  while(it) {
    // store the link for fast lookup
    var2prem.insert(cl_no,it->head());

    // corresponding assumption
    ass.push(mkLit(cl_no)); // posive as the assumption

    // allocate the var for the clause
    ALWAYS(solver.newVar() == cl_no);

    cl_no++;
    it=it->tail();
  }

  // from now on, offset will mark the translation of premises' original variables to the ones in solver here
  int offset = cl_no; // first var in the solver that was not allocated yet

  // smallest var not allocated yet
  int curmax = cl_no;

  // start counting from 0 and traversing from the beginning again
  cl_no = 0;
  it= premises;
  while(it) {
    SATClause* cl = it->head();

    static vec<Lit> mcl;
    mcl.clear();

    // translate the clause to minisat's language (shift vars by offset)
    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral l = (*cl)[i];
      int var = offset + l.var();

      // make sure vars are allocated
      while (var >= curmax) {
        solver.newVar();
        curmax++;
      }

      mcl.push(mkLit(var,!l.positive()));
    }

    // add one extra assumption literal
    mcl.push(mkLit(cl_no,true)); // negated in the clause

    solver.addClause(mcl);

    cl_no++;
    it=it->tail();
  }

  // add assumptions from assumps
  SATLiteralStack::Iterator ait(assumps);
  while (ait.hasNext()) {
    SATLiteral l = ait.next();
    int var = offset + l.var();

    ASS_L(var,curmax);

    ass.push(mkLit(var,!l.positive()));
  }

  // solve
  ALWAYS(!solver.solve(ass)); // should be unsat

  SATClauseList* result = SATClauseList::empty();

  // extract the used ones
  Minisat::LSet& conflict = solver.conflict;
  for (int i = 0; i < conflict.size(); i++) {
    int v = var(conflict[i]);

    SATClause* cl;

    if (var2prem.find(v,cl)) {
      SATClauseList::push(cl,result);
    } // it could also be one of the "assumps"
  }
  return result;
}

void MinisatInterfacing::interpolateViaAssumptions(unsigned maxVar, const SATClauseStack& first, const SATClauseStack& second, SATClauseStack& result)
{
  Minisat::Solver solver_first;
  Minisat::Solver solver_second;

  // TODO: this may be quite wasteful for at least two reasons:
  // 1) 1..maxVar may be a large superset of symb(first \cup second)
  // 2) symb(first \cup second) may be a large superset of symb(second)
  // However, making sure variables are not wasted would require
  // setting up various renamings to maintain correspondence
  // between literals in the solvers
  for(unsigned v = 0; v <= maxVar; v++) { // ... and variable 0 will not be used either
    solver_first.newVar();
    solver_second.newVar();
  }

  DArray<bool> varOfFirst;
  varOfFirst.expand(maxVar+1,false);

  vec<Lit> tmp;

  // load first into solver_first and mark in varOfFirst
  SATClauseStack::ConstIterator it1(first);
  while(it1.hasNext()) {
    SATClause* cl = it1.next();

    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral l = (*cl)[i];
      varOfFirst[l.var()] = true;
      tmp.push(mkLit(l.var(),!l.positive()));
    }

    solver_first.addClause(tmp);
    tmp.clear();
  }

  // load second into solver_second
  SATClauseStack::ConstIterator it2(second);
  while(it2.hasNext()) {
    SATClause* cl = it2.next();

    unsigned clen=cl->length();
    for(unsigned i=0;i<clen;i++) {
      SATLiteral l = (*cl)[i];
      tmp.push(mkLit(l.var(),!l.positive()));
    }

    solver_second.addClause(tmp);
    tmp.clear();
  }

  SATLiteralStack vlits;

  // generate the interpolant clauses
  while (solver_first.solve()) {
    // turn model into assumptions for solver_second
    for (int i = 1; i <= (int)maxVar; i++) {
      if (varOfFirst[i]) {
        tmp.push(mkLit(i,solver_first.model[i]==l_False));
      }
    }

    NEVER(solver_second.solve(tmp));
    tmp.clear();

    // conflict is a new clause to put into result and solver_first to look for a different model
    LSet& conflict = solver_second.conflict;
    for (int i = 0; i < conflict.size(); i++) {
      Lit l = conflict[i];

      tmp.push(l);
      vlits.push(SATLiteral(var(l),sign(l) ? 0 : 1));
    }

    solver_first.addClause(tmp);
    tmp.clear();

    result.push(SATClause::fromStack(vlits));
    vlits.reset();
  }
}


} // namespace SAT

