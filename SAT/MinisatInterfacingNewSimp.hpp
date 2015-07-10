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

class MinisatInterfacingNewSimp : public PrimitiveProofRecordingSATSolver
{
public: 
  CLASS_NAME(MinisatInterfacingNewSimp);
  USE_ALLOCATOR(MinisatInterfacingNewSimp);
  
	MinisatInterfacingNewSimp(const Shell::Options& opts, bool generateProofs=false);

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in a clause, each variable occurs at most once.
   */
  virtual void addClause(SATClause* cl) override;
  
  /**
   * Opportunity to perform in-processing of the clause database.
   *
   * (Minisat deletes unconditionally satisfied clauses.)
   */
  virtual void simplify() override {
    CALL("MinisatInterfacingNewSimp::simplify");
    _solver.simplify();
  }

  virtual Status solve(unsigned conflictCountLimit) override;
  
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var);

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var);
  /**
   * Collect zero-implied literals.
   *
   * Can be used in SATISFIABLE and UNKNOWN state.
   *
   * @see isZeroImplied()
   */
  virtual void collectZeroImplied(SATLiteralStack& acc);
  /**
   * Return a valid clause that contains the zero-implied literal
   * and possibly the assumptions that implied it. Return 0 if @c var
   * was an assumption itself.
   * If called on a proof producing solver, the clause will have
   * a proper proof history.
   */
  virtual SATClause* getZeroImpliedCertificate(unsigned var);

  virtual void ensureVarCount(unsigned newVarCnt) override;
  
  virtual unsigned newVar() override;
  
  virtual void suggestPolarity(unsigned var, unsigned pol) override {
    // 0 -> true which means negated, e.g. false in the model
    bool mpol = pol ? false : true; 
    _solver.suggestPolarity(vampireVar2Minisat(var),mpol);
  }
  
  /**
   * Add an assumption into the solver.
   */
  virtual void addAssumption(SATLiteral lit);
  
  virtual void retractAllAssumptions() {
    _assumptions.clear();
    _status = UNKNOWN;
  };
  
  virtual bool hasAssumptions() const {
    return (_assumptions.size() > 0);
  };

 /**
  * Record the association between a SATLiteral var and a Literal
  * In TWLSolver this is used for computing niceness values
  */
  virtual void recordSource(unsigned satlitvar, Literal* lit) {
    // unsupported by minisat; intentionally no-op
  };
  
  Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool) override;

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
};

}//end SAT namespace

 #endif /*MinisatInterfacingNewSimp*/
