
/*
 * File Z3Interfacing.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
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

  struct UninterpretedForZ3Exception : public ThrowableBase
  {
    UninterpretedForZ3Exception() 
    {
      CALL("Z3Interfacing::UninterpretedForZ3Exception::UninterpretedForZ3Exception");
    }
  };

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

  void addClause(SATClause* cl, bool withGuard);
  void addClause(SATClause* cl) override { addClause(cl,false); }

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

  void ensureVarCount(unsigned newVarCnt) override {
    CALL("Z3Interfacing::ensureVarCnt");

    while (_varCnt < newVarCnt) {
      newVar();
    }
  }

  unsigned newVar() override;

  // Currently not implemented for Z3
  virtual void suggestPolarity(unsigned var, unsigned pol) override {}
  
  void addAssumption(SATLiteral lit, bool withGuard);
  virtual void addAssumption(SATLiteral lit) override { addAssumption(lit,false); }
  virtual void retractAllAssumptions() override { _assumptions.resize(0); }
  virtual bool hasAssumptions() const override { return !_assumptions.empty(); }

  Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned,bool,bool);
  virtual Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned c, bool p) override
  { return solveUnderAssumptions(assumps,c,p,false); }

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

  void reset(){
    sat2fo.reset();
    _solver.reset();
    _status = UNKNOWN; // I set it to unknown as I do not reset
  }
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
        return -to_real(to_int(-e));
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
  void addIntNonZero(z3::expr);
  void addRealNonZero(z3::expr);

public:
  // not sure why this one is public
  z3::expr getz3expr(Term* trm,bool islit,bool&nameExpression,  Stack<unsigned>& sortsForMergeAxioms, bool withGuard=false);
  Term* evaluateInModel(Term* trm);

private:
  z3::expr getRepresentation(SATLiteral lit,bool withGuard);

  Status _status;
  z3::context _context;
  z3::solver _solver;
  z3::model _model;

  z3::expr_vector _assumptions;
  bool _unsatCoreForAssumptions;

  bool _showZ3;
  bool _unsatCoreForRefutations;

  DHSet<unsigned> _namedExpressions;

  DHMap<unsigned,z3::expr*> _mergeAssumptions; //when translating array merge, we need to add an axiom for each array sort merge operation
  
  z3::expr getNameExpr(unsigned var){
    vstring name = "v"+Lib::Int::toString(var);
    return  _context.bool_const(name.c_str());
  }
  // careful: keep native constants' names distinct from the above ones (hence the "c"-prefix below)
  z3::expr getNameConst(const vstring& symbName, z3::sort srt){
    vstring name = "c"+symbName;
    return _context.constant(name.c_str(),srt);
  }

  Term* representNumeral(z3::expr *expr, unsigned sort);
  bool representSort(const z3::sort &sort, unsigned& vsort);
  Term* representArray(z3::expr& assigment);

  void addArrayMergeAxiom(unsigned vsort);

};

}//end SAT namespace

#endif /* if VZ3 */
#endif /*Z3Interfacing*/
