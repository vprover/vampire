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
 * @file MinisatInterfacing.hpp
 * Defines class MinisatInterfacing
 */
#ifndef __MinisatInterfacing__
#define __MinisatInterfacing__

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"

#include "Minisat/core/Solver.h"
#include "Minisat/simp/SimpSolver.h"

namespace SAT{

template<typename MinisatSolver = Minisat::Solver>
class MinisatInterfacing : public SATSolver
{
public:
  static const unsigned VAR_MAX = std::numeric_limits<Minisat::Var>::max() / 2;

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in a clause, each variable occurs at most once.
   */
  void addClause(SATClause* cl) override;

  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  VarAssignment getAssignment(unsigned var) override;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  bool isZeroImplied(unsigned var) override;

  void ensureVarCount(unsigned newVarCnt) override;

  unsigned newVar() override;

  void suggestPolarity(unsigned var, unsigned pol) override {
    // 0 -> true which means negated, e.g. false in the model
    bool mpol = pol ? false : true; 
    _solver.suggestPolarity(vampireVar2Minisat(var),mpol);
  }

  Status solveUnderAssumptionsLimited(const SATLiteralStack& assumps, unsigned conflictCountLimit) override;
  SATLiteralStack failedAssumptions() override;

  /**
   * Use minisat and solving under assumptions to minimize the given set of premises (= unsat core extraction).
   *
   * Assumes @b premises in conjunction with @b assumps unsat.
   * Returns a "small" subset of premises which is still unsat under assumps.
   */
  static SATClauseList* minimizePremiseList(SATClauseList* premises, SATLiteralStack& assumps);

  /**
   * Assuming that @b first together with @b second is inconsistent,
   * produce (in @b result) a set of clauses over the signature of @b first,
   * such that @b second |= @b result and
   * @b first together with @b result is also inconsistent.
   */
  static void interpolateViaAssumptions(unsigned maxVar, const SATClauseStack& first, const SATClauseStack& second, SATClauseStack& result);

  SATClauseList *minimizePremises(SATClauseList *premises) override {
    SATLiteralStack assumps;
    for(int i = 0; i < _assumptions.size(); i++)
      assumps.push(minisatLit2Vampire(_assumptions[i]));
    return minimizePremiseList(premises, assumps);
  }

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
  
  /* sign=true in minisat means "negated" in vampire */
  const SATLiteral minisatLit2Vampire(Minisat::Lit mlit) {
    return SATLiteral(minisatVar2Vampire(Minisat::var(mlit)),Minisat::sign(mlit) ? 0 : 1);
  }
  
private:
  Status _status = Status::SATISFIABLE;
  Minisat::vec<Minisat::Lit> _assumptions;
  MinisatSolver _solver;
};

using MinisatInterfacingNewSimp = MinisatInterfacing<Minisat::SimpSolver>;

}//end SAT namespace

 #endif /*MinisatInterfacing*/
