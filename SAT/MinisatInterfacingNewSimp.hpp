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
 * @file MinisatInterfacingNewSimp.hpp
 * Defines class MinisatInterfacingNewSimp
 */
#ifndef __MinisatInterfacingNewSimp__
#define __MinisatInterfacingNewSimp__

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "Minisat/simp/SimpSolver.h"

namespace SAT{

class MinisatInterfacingNewSimp : public SATSolverWithAssumptions
{
public:
  static const unsigned VAR_MAX;

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in a clause, each variable occurs at most once.
   */
  virtual void addClause(SATClause* cl) override;

  virtual Status solveLimited(unsigned conflictCountLimit) override;
  
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var) override;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var) override;

  virtual void ensureVarCount(unsigned newVarCnt) override;
  
  virtual unsigned newVar() override;
  
  virtual void suggestPolarity(unsigned var, unsigned pol) override {
    // 0 -> true which means negated, e.g. false in the model
    bool mpol = pol ? false : true; 
    _solver.suggestPolarity(vampireVar2Minisat(var),mpol);
  }

  Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) override;
  SATLiteralStack failedAssumptions() override;

  virtual SATClause* getRefutation() override { ASSERTION_VIOLATION; }

protected:
  void solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit = UINT_MAX);
  
  Minisat::Var vampireVar2Minisat(unsigned vvar) {
    ASS_G(vvar,0); ASS_LE(vvar,(unsigned)_solver.nVars());
    return (vvar-1);
  }
  
  unsigned minisatVar2Vampire(Minisat::Var mvar) {
    return (unsigned)(mvar+1);
  }
  
  const Minisat::Lit vampireLit2Minisat(SATLiteral vlit) {
    return Minisat::mkLit(vampireVar2Minisat(vlit.var()),!vlit.positive()); 
  }
  
  /* sign=trun in minisat means "negated" in vampire */
  const SATLiteral minisatLit2Vampire(Minisat::Lit mlit) {
    return SATLiteral(minisatVar2Vampire(Minisat::var(mlit)),Minisat::sign(mlit) ? 0 : 1);
  }
  
private:
  Status _status = Status::SATISFIABLE;
  Minisat::vec<Minisat::Lit> _assumptions;
  Minisat::SimpSolver _solver;
};

}//end SAT namespace

 #endif /*MinisatInterfacingNewSimp*/
