/**
 * @file Z3Interfacing.hpp
 * Defines class Z3Interfacing
 */

#ifndef __Z3Interfacing__
#define __Z3Interfacing__

#if VZ3

#include "Lib/DHMap.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"
#include "SAT2FO.hpp"

#include "z3++.h"
#include "z3_api.h"

namespace SAT{

class Z3Interfacing : public SATSolver
{
public: 
  CLASS_NAME(Z3Interfacing);
  USE_ALLOCATOR(Z3Interfacing);
  
  Z3Interfacing(const Shell::Options& opts, SAT2FO& s2f, bool generateProofs=false);

  /**
   * Can be called only when all assumptions are retracted
   *
   * A requirement is that in each clause, each variable occurs at most once.
   */
  virtual void addClauses(SATClauseIterator cit);
  void addClause(SATClause* cl);

  virtual Status solve(unsigned conflictCountLimit) override;
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

  // Note required for Z3
  virtual void ensureVarCnt(unsigned newVarCnt){}

  // Currently not implemented for Z3
  virtual void suggestPolarity(unsigned var, unsigned pol){} 
  virtual void forcePolarity(unsigned var, unsigned pol) {}
  
  
  
  /**
   * Add an assumption into the solver. If conflictCountLimit==0,
   * do only unit propagation, if conflictCountLimit==UINT_MAX, do
   * full satisfiability check, and for values in between, restrict
   * the number of conflicts, and in case it is reached, stop with
   * solving and assign the status to UNKNOWN.
   */
  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  
  virtual void retractAllAssumptions(){} 
  
  virtual bool hasAssumptions() const{ return false; }

  virtual SATClause* getRefutation();

 /**
  * Record the association between a SATLiteral var and a Literal
  * In TWLSolver this is used for computing niceness values
  */
  virtual void recordSource(unsigned satlitvar, Literal* lit) {
    // unsupported by Z3; intentionally no-op
  };
  
private:

  // Memory belongs to Splitter
  SAT2FO& sat2fo;

  DHMap<unsigned,Z3_sort> _sorts;
  z3::sort getz3sort(unsigned s);
public:
  z3::expr getz3expr(Term* trm,bool islit);
private:
  z3::expr getRepresentation(SATLiteral lit);

  Status _status;
  z3::context _context;
  z3::solver _solver;
  z3::model _model;
  SATClauseList* _addedClauses;
  bool _showZ3;
};

}//end SAT namespace

#endif /* if VZ3 */
#endif /*Z3Interfacing*/
