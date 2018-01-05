
/*
 * File CVC4Interfacing.hpp.
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
 * @file CVC4Interfacing.hpp
 * Defines class CVC4Interfacing
 */

#ifndef __CVC4Interfacing__
#define __CVC4Interfacing__

#include "Lib/DHMap.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"
#include "SAT2FO.hpp"

#include "z3++.h"
#include "z3_api.h"

#include "cvc4.h"

namespace SAT{

  struct UninterpretedForCVC4Exception : public ThrowableBase
  {
    UninterpretedForCVC4Exception()
    {
      CALL("CVC4Interfacing::UninterpretedForCVC4Exception::UninterpretedForCVC4Exception");
    }
  };

class CVC4Interfacing : public PrimitiveProofRecordingSATSolver
{
public: 
  CLASS_NAME(CVC4Interfacing);
  USE_ALLOCATOR(CVC4Interfacing);
  
  /**
   * If @c unsatCoresForAssumptions is set, the solver is configured to use
   * the "unsat-core" option (may negatively affect performance) and uses
   * this feature to extract a subset of used assumptions when
   * called via solveUnderAssumptions.
   */
  CVC4Interfacing(const Shell::Options& opts, SAT2FO& s2f);

  void addClause(SATClause* cl) override;

  virtual Status solve(unsigned conflictCountLimit) override;
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  VarAssignment getAssignment(unsigned var) override;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  bool isZeroImplied(unsigned var) override { return false; }
  /**
   * Collect zero-implied literals.
   *
   * Can be used in SATISFIABLE and UNKNOWN state.
   *
   * @see isZeroImplied()
   */
  void collectZeroImplied(SATLiteralStack& acc) override { NOT_IMPLEMENTED; }
  /**
   * Return a valid clause that contains the zero-implied literal
   * and possibly the assumptions that implied it. Return 0 if @c var
   * was an assumption itself.
   * If called on a proof producing solver, the clause will have
   * a proper proof history.
   */
  SATClause* getZeroImpliedCertificate(unsigned var) override {
    NOT_IMPLEMENTED;

    return 0;
  }

  void ensureVarCount(unsigned newVarCnt) override {
    CALL("CVC4Interfacing::ensureVarCnt");

    while (_varCnt < newVarCnt) {
      newVar();
    }
  }

  unsigned newVar() override;

  // Currently not implemented for CVC4
  virtual void suggestPolarity(unsigned var, unsigned pol) override {}
  virtual void addAssumption(SATLiteral lit) override { NOT_IMPLEMENTED; }
  virtual void retractAllAssumptions() override { NOT_IMPLEMENTED; }
  virtual bool hasAssumptions() const override { NOT_IMPLEMENTED; }

 /**
  * Record the association between a SATLiteral var and a Literal
  * In TWLSolver this is used for computing niceness values
  */
  virtual void recordSource(unsigned satlitvar, Literal* lit) override {
    // unsupported by CVC4; intentionally no-op
  };
  
  /**
   * The set of inserted clauses may not be propositionally UNSAT
   * due to theory reasoning inside CVC4.
   * We cannot later minimize this set with minisat.
   *
   * TODO: think of extracting true refutation from Z3 instead.
   */
  SATClauseList* getRefutationPremiseList() override{ return 0; } 

  SATClause* getRefutation() override;  

  // for the theory instantiation inference (separate concern)
  /*
  Term* evaluateInModel(Term* trm);
  void reset() {
    sat2fo.reset();
    _solver.reset();
    _status = UNKNOWN; // I set it to unknown as I do not reset
  }
  */

private:
  CVC4::ExprManager _manager;
  CVC4::SmtEngine _engine;

  CVC4::Expr createRepresentation(unsigned satVar);

  typedef DHMap<unsigned,CVC4::Expr> VarMap;

  VarMap _representations; // from the SAT variables to CVC4 expressions

  /*
   * Recursively translate vampire term (which can be a literal) to a CVC4 expression.
   * Vampire variables are looked up in vars, which will get extended if no binding is found.
   * Polarity of the literal (if applicable) is ignored.
   */
  CVC4::Expr getRepr(Term* trm, VarMap& vars);

  CVC4::Type getCVC4sort(unsigned srt);

  // Fresh is just to stress what mkVar does. Not that we would like it that much
  CVC4::Expr createFreshExprName(unsigned satVar) {
    CALL("CVC4Interfacing::createFreshExprName");
    vstring name = "v"+Lib::Int::toString(satVar);
    return _manager.mkVar(string(name.c_str()),_manager.booleanType()); // mkVar creates a constant, don't worry!
  }

  // Fresh is just to stress what mkVar does. Not that we would like it that much
  CVC4::Expr createFreshConst(const vstring& symbName, CVC4::Type srt) {
    CALL("CVC4Interfacing::createFreshConst");
    vstring name = "c"+symbName;
    return _manager.mkVar(string(name.c_str()),srt); // mkVar creates a constant, don't worry!
  }

  typedef DHMap<std::pair<unsigned,unsigned>,  // vampire symbol id, vampire sort id
                                  CVC4::Expr> SortedSymbolMap;

  SortedSymbolMap _constants;
  SortedSymbolMap _nonZeroAritySymbols; // can be both functions and predicates, the attached sort is the "range sort", just to distinguish function symbols and predicate symbols

  DHMap<unsigned, CVC4::Type> _sorts;

  bool _showCVC4;

  // for properly managing newVar calls
  unsigned _varCnt;

  // Memory belongs to Splitter
  SAT2FO& sat2fo;

  Status _status;

  bool _unsatCoreForRefutations;
};

}//end SAT namespace

#endif /*CVC4Interfacing*/
