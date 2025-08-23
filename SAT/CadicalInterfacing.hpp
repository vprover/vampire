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
 * @file CadicalInterfacing.hpp
 * Defines class CadicalInterfacing
 */
#ifndef __CadicalInterfacing__
#define __CadicalInterfacing__

#include <filesystem>

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "MinisatInterfacing.hpp"

#include "cadical/src/cadical.hpp"

namespace SAT{

class CadicalInterfacing : public SATSolver
{
public:
  CadicalInterfacing();

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in a clause, each variable occurs at most once.
   */
  virtual void addClause(SATClause* cl) override;

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var) override;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var) override;

  virtual void ensureVarCount(unsigned newVarCnt) override { _next = std::max(_next, int(newVarCnt) + 1); }

  virtual unsigned newVar() override { return _next++; }

  virtual void suggestPolarity(unsigned var, unsigned pol) override {
    _solver.reserve(vampire2Cadical(true, var));
    _solver.phase(vampire2Cadical(pol, var));
  }

  Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) override;
  SATLiteralStack failedAssumptions() override;

  SATClauseList *minimizePremises(SATClauseList *premises) override {
    SATLiteralStack assumps;
    for(int l : _assumptions)
      assumps.push(cadical2Vampire(l));
    return MinisatInterfacing<>::minimizePremiseList(premises, assumps);
  }

  /*
   * run CaDiCaL on the assumed-unsatisfiable `premises` and log a proof
   * returns a path to the (binary) DRAT proof
   */
  static std::filesystem::path drat(SATClauseList* premises);

protected:
  void solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit = UINT_MAX);

private:
  static int vampire2Cadical(bool polarity, unsigned atom) {
    ASS_NEQ(atom, 0)
    return polarity ? atom : -(int)(atom);
  }

  static int vampire2Cadical(SATLiteral vampire) {
    return vampire2Cadical(vampire.positive(), vampire.var());
  }

  static SATLiteral cadical2Vampire(int cadical) {
    return SATLiteral(std::abs(cadical), cadical < 0);
  }

  int _next = 1;
  Status _status = Status::SATISFIABLE;
  std::vector<int> _assumptions;
  CaDiCaL::Solver _solver;
};

}//end SAT namespace

 #endif /*CadicalInterfacing*/
