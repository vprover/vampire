/**
 * @file MinisatInterfacing.hpp
 * Defines class MinisatInterfacing
 */
#ifndef __MinisatInterfacing__
#define __MinisatInterfacing__

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"

#include "Minisat/core/Solver.h"

namespace SAT{

class MinisatInterfacing : public SATSolver
{
public: 
  CLASS_NAME(MinisatInterfacing);
  USE_ALLOCATOR(MinisatInterfacing);
  
	MinisatInterfacing(const Shell::Options& opts, bool generateProofs=false);

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in each clause, each variable occurs at most once.
   */
  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate);
  virtual Status getStatus() { return _status; }
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var);

  /**
   * Try to find another assignment which is likely to be different from the current one
   *
   * @pre Solver must be in SATISFIABLE status
   */
  virtual void randomizeAssignment();

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

  virtual void ensureVarCnt(unsigned newVarCnt);
  
  /**
   * Add an assumption into the solver. If conflictCountLimit==0,
   * do only unit propagation, if conflictCountLimit==UINT_MAX, do
   * full satisfiability check, and for values in between, restrict
   * the number of conflicts, and in case it is reached, stop with
   * solving and assign the status to UNKNOWN.
   */
  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  
  virtual void retractAllAssumptions() {
    _assumptions.clear();
    _status = UNKNOWN;
  };
  
  virtual bool hasAssumptions() const {
    return (_assumptions.size() > 0);
  };

  virtual SATClause* getRefutation();

 /**
  * Record the association between a SATLiteral var and a Literal
  * In TWLSolver this is used for computing niceness values
  */
  virtual void recordSource(unsigned satlitvar, Literal* lit) {
    // unsupported by minisat; intentionally no-op
  };
  
protected:    
  void solveModuloAssumptionsAndSetStatus(unsigned conflictCountLimit = UINT_MAX);
  
  static Minisat::Var vampireVar2Minisat(unsigned vvar) {
    // "identity" for now, but does variable 0 really exist in vampire?
    return vvar;
  }
  
  static unsigned minisatVar2Vampire(Minisat::Var mvar) {
    // "identity" for now, but does variable 0 really exist in vampire?
    return (unsigned)mvar;
  }
  
  static const Minisat::Lit vampireLit2Minisat(SATLiteral vlit) {
    return Minisat::mkLit(vampireVar2Minisat(vlit.var()),vlit.isNegative()); 
  }
  
  /* sign=trun in minisat means "negated" in vampire */
  static const SATLiteral minisatLit2Vampire(Minisat::Lit mlit) {
    return SATLiteral(minisatVar2Vampire(Minisat::var(mlit)),Minisat::sign(mlit) ? 0 : 1);            
  }
  
private:
  Status _status;
  Minisat::vec<Minisat::Lit> _assumptions;  
  Minisat::Solver _solver;
  
  // to be used for the premises of a refutation
  // TODO: who should now free the list? 
  // (and when it's passed as part of the refutation?, perhaps more than once?) 
  // -- consider moving responsibility to the caller
  SATClauseList* _addedClauses;
};

}//end SAT namespace

 #endif /*MinisatInterfacing*/
