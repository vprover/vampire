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

// For limitMemory
#include <csignal>
#include <sys/time.h>
#include <sys/resource.h>

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "Minisat/simp/SimpSolver.h"

namespace SAT{

class MinisatInterfacingNewSimp : public SATSolverWithAssumptions
{
public:
  CLASS_NAME(MinisatInterfacingNewSimp);
  USE_ALLOCATOR(MinisatInterfacingNewSimp);
  
  static const unsigned VAR_MAX;

	MinisatInterfacingNewSimp(const Shell::Options& opts, bool generateProofs=false);

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in a clause, each variable occurs at most once.
   */
  void addClause(SATClause* cl) final;
  
  /**
   * Opportunity to perform in-processing of the clause database.
   *
   * (Minisat deletes unconditionally satisfied clauses.)
   */
  void simplify() final {
    CALL("MinisatInterfacingNewSimp::simplify");
    _solver.simplify();
  }

  Status solve(unsigned conflictCountLimit) final;
  
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  VarAssignment getAssignment(unsigned var) final;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  bool isZeroImplied(unsigned var) final;
  /**
   * Collect zero-implied literals.
   *
   * Can be used in SATISFIABLE and UNKNOWN state.
   *
   * @see isZeroImplied()
   */
  void collectZeroImplied(SATLiteralStack& acc) final;
  /**
   * Return a valid clause that contains the zero-implied literal
   * and possibly the assumptions that implied it. Return 0 if @c var
   * was an assumption itself.
   * If called on a proof producing solver, the clause will have
   * a proper proof history.
   */
  SATClause* getZeroImpliedCertificate(unsigned var) final;

  void ensureVarCount(unsigned newVarCnt) final;
  
  unsigned newVar() final;
  
  void suggestPolarity(unsigned var, unsigned pol) final {
    // 0 -> true which means negated, e.g. false in the model
    bool mpol = pol ? false : true; 
    _solver.suggestPolarity(vampireVar2Minisat(var),mpol);
  }
  
  /**
   * Add an assumption into the solver.
   */
  void addAssumption(SATLiteral lit) final;
  
  void retractAllAssumptions() final {
    _assumptions.clear();
    _status = UNKNOWN;
  };
  
  bool hasAssumptions() const final {
    return (_assumptions.size() > 0);
  };

  Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool) final;

  SATClause* getRefutation() final { ASSERTION_VIOLATION; }

  static void reportMinisatOutOfMemory();

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
    return Minisat::mkLit(vampireVar2Minisat(vlit.var()),vlit.isNegative()); 
  }
  
  /* sign=trun in minisat means "negated" in vampire */
  const SATLiteral minisatLit2Vampire(Minisat::Lit mlit) {
    return SATLiteral(minisatVar2Vampire(Minisat::var(mlit)),Minisat::sign(mlit) ? 0 : 1);            
  }
  
private:
  Status _status;
  Minisat::vec<Minisat::Lit> _assumptions;  
  Minisat::SimpSolver _solver;

  //Copied from Minisat/utils/System.cc
  static void limitMemory(uint64_t max_mem_mb)
  {
      // Set limit on virtual memory:
      if (max_mem_mb != 0){
          rlim_t new_mem_lim = (rlim_t)max_mem_mb * 1024*1024;
          rlimit rl;
          getrlimit(RLIMIT_AS, &rl);
          if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
              rl.rlim_cur = new_mem_lim;
              if (setrlimit(RLIMIT_AS, &rl) == -1)
                  printf("WARNING! Could not set resource limit: Virtual memory.\n");
          }
      }
  }
};

}//end SAT namespace

 #endif /*MinisatInterfacingNewSimp*/
