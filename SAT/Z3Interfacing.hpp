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

class Z3Interfacing : public PrimitiveProofRecordingSATSolver
{
public: 
  CLASS_NAME(Z3Interfacing);
  USE_ALLOCATOR(Z3Interfacing);
  
  /**
   * If @c unsatCoresForAssumptions is set, the solver is configured to use
   * the "unsat-core" option (may negatively affect performance) and uses
   * this feature to extract a subset of used assumptions when
   * called via solveUnderAssumptions.
   */
  Z3Interfacing(const Shell::Options& opts, SAT2FO& s2f, bool unsatCoresForAssumptions = false);

  void addClause(SATClause* cl) override;

  virtual Status solve(unsigned conflictCountLimit) override;
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var) override;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var) override;
  /**
   * Collect zero-implied literals.
   *
   * Can be used in SATISFIABLE and UNKNOWN state.
   *
   * @see isZeroImplied()
   */
  virtual void collectZeroImplied(SATLiteralStack& acc) override;
  /**
   * Return a valid clause that contains the zero-implied literal
   * and possibly the assumptions that implied it. Return 0 if @c var
   * was an assumption itself.
   * If called on a proof producing solver, the clause will have
   * a proper proof history.
   */
  virtual SATClause* getZeroImpliedCertificate(unsigned var) override;

  // Not required for Z3, but let's keep track of the counter
  virtual void ensureVarCount(unsigned newVarCnt) override {
    CALL("Z3Interfacing::ensureVarCnt");
    _varCnt = max(newVarCnt,_varCnt);
  }

  virtual unsigned newVar() override {
    CALL("Z3Interfacing::newVar");
    return ++_varCnt;
  }

  // Currently not implemented for Z3
  virtual void suggestPolarity(unsigned var, unsigned pol) override {}
  
  virtual void addAssumption(SATLiteral lit) override;
  virtual void retractAllAssumptions() override { _assumptions.resize(0); }
  virtual bool hasAssumptions() const override { return !_assumptions.empty(); }

  virtual Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned, bool) override;

 /**
  * Record the association between a SATLiteral var and a Literal
  * In TWLSolver this is used for computing niceness values
  */
  virtual void recordSource(unsigned satlitvar, Literal* lit) override {
    // unsupported by Z3; intentionally no-op
  };
  
  /**
   * The set of inserted clauses may not be propositionally UNSAT
   * due to theory reasoning inside Z3.
   * We cannot later minimize this set with minisat.
   *
   * TODO: think of extracting true refutation from Z3 instead.
   */
  SATClauseList* getRefutationPremiseList() override{ return 0; } 

  SATClause* getRefutation() override;  

private:
  // just to conform to the interface
  unsigned _varCnt;

  // Memory belongs to Splitter
  SAT2FO& sat2fo;

  //DHMap<unsigned,Z3_sort> _sorts;
  z3::sort getz3sort(unsigned s);

  // Helper funtions for the translation
  z3::expr to_int(z3::expr e) {
        return z3::expr(e.ctx(), Z3_mk_real2int(e.ctx(), e));
  }
  z3::expr to_real(z3::expr e) {
        return z3::expr(e.ctx(), Z3_mk_int2real(e.ctx(), e));
  }
  z3::expr ceiling(z3::expr e){
        return -to_real(to_int((e)));
  }
  z3::expr is_even(z3::expr e) {
        z3::context& ctx = e.ctx();
        z3::expr two = ctx.int_val(2);
        z3::expr m = z3::expr(ctx, Z3_mk_mod(ctx, e, two));
        return m == 0;
  }

  z3::expr truncate(z3::expr e) {
        return ite(e >= 0, to_int(e), ceiling(e));
  }

  void addTruncatedOperations(z3::expr_vector, Interpretation qi, Interpretation ti, unsigned srt);
  void addFloorOperations(z3::expr_vector, Interpretation qi, Interpretation ti, unsigned srt);

public:
  // not sure why this one is public
  z3::expr getz3expr(Term* trm,bool islit,bool&nameExpression);
  Term* evaluateInModel(Term* trm);
private:
  z3::expr getRepresentation(SATLiteral lit);

  Status _status;
  z3::context _context;
  z3::solver _solver;
  z3::model _model;

  z3::expr_vector _assumptions;
  bool _unsatCoreForAssumptions;

  bool _showZ3;
  bool _unsatCoreForRefutations;

  DHSet<unsigned> _namedExpressions; 
  z3::expr getNameExpr(unsigned var){
    vstring name = "v"+Lib::Int::toString(var);
    return  _context.bool_const(name.c_str());
  }

};

}//end SAT namespace

#endif /* if VZ3 */
#endif /*Z3Interfacing*/
