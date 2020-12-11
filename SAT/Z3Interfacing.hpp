
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
 */
/**
 * @file Z3Interfacing.hpp
 * Defines class Z3Interfacing
 */

#ifndef __Z3Interfacing__
#define __Z3Interfacing__

#if VZ3

/* an (imperfect and under development) version of tracing the Z3 interface
 *  so that vampire can be "factored-out" of runs which cause particular Z3
 *  behaviour. Should be useful for producing MWEs for the Z3 people.
 */
#define PRINT_CPP(X) // cout << X << endl;

#include "Lib/DHMap.hpp"
#include "Lib/BiMap.hpp"
#include "Lib/Set.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"
#include "SAT2FO.hpp"
#include "Lib/Option.hpp"
#include "Lib/Coproduct.hpp"

#define __EXCEPTIONS 1
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
  Z3Interfacing(SAT2FO& s2f, bool showZ3, bool unsatCoreForRefutations, bool unsatCoresForAssumptions);
  ~Z3Interfacing();

  static char const* z3_full_version();

  void addClause(SATClause* cl, bool withGuard);
  void addClause(SATClause* cl) override { addClause(cl,false); }

  virtual Status solve();
  virtual Status solve(unsigned conflictCountLimit) override { return solve(); };
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
  using FuncId = unsigned;
  using PredId = unsigned;
  using SortId = unsigned;

  struct FuncOrPredId 
  {
    explicit FuncOrPredId(unsigned id, bool isPredicate) : id(id), isPredicate(isPredicate) {}
    explicit FuncOrPredId(Term* term) : FuncOrPredId(term->functor(), term->isLiteral()) {}
    static FuncOrPredId function(FuncId id) { return FuncOrPredId ( id, false ); } 
    static FuncOrPredId predicate(PredId id) { return FuncOrPredId ( id, true ); } 
    unsigned id;
    bool isPredicate;
    unsigned hash() { return Lib::HashUtils::combine(id, isPredicate); }
    friend bool operator==(FuncOrPredId const& l, FuncOrPredId const& r)
    { return l.id == r.id && l.isPredicate == r.isPredicate; }
  };

private:
  struct NoMeta {};

  struct DestructorMeta
  { z3::func_decl selector; };

  struct Z3FuncEntry {
    using Metadata = Coproduct<NoMeta, DestructorMeta>;
    z3::func_decl self;
    Metadata metadata;

    static Z3FuncEntry plain(z3::func_decl d) 
    { return  Z3FuncEntry { .self = d, .metadata = Metadata(NoMeta {}) }; }

    static Z3FuncEntry destructor(z3::func_decl destr, z3::func_decl sel) 
    { return  Z3FuncEntry { .self = destr, .metadata = Metadata(DestructorMeta { .selector = sel, }) }; }
  };


  Map<unsigned,z3::sort> _sorts;
  struct Z3Hash {
    static unsigned hash(z3::func_decl const& c) { return c.hash(); }
    static bool equals(z3::func_decl const& l, z3::func_decl const& r) { return z3::eq(l,r); }
  };
  Map<z3::func_decl, FuncOrPredId, Z3Hash   > _fromZ3;
  Map<FuncOrPredId,  Z3FuncEntry,  Lib::Hash> _toZ3;
  Set<SortId> _createdTermAlgebras;

  z3::func_decl const& findConstructor(FuncId id);
  void createTermAlgebra(Shell::TermAlgebra&);

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

  // not sure why this one is public
  friend struct ToZ3Expr;
  friend struct EvaluateInModel;
  z3::expr getz3expr(Term* trm, bool&nameExpression, bool withGuard=false);
public:
  Term* evaluateInModel(Term* trm);
#ifdef VDEBUG
  z3::model& getModel() { return _model; }
#endif

private:

  z3::expr getRepresentation(SATLiteral lit,bool withGuard);

  // just to conform to the interface
  unsigned _varCnt;
  // Memory belongs to Splitter
  SAT2FO& sat2fo;

  Status _status;
  z3::config _config;
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

    PRINT_CPP("exprs.push_back(c.bool_const(\""<< name << "\"));")

    return  _context.bool_const(name.c_str());
  }
  // careful: keep native constants' names distinct from the above ones (hence the "c"-prefix below)
  z3::expr getNameConst(const vstring& symbName, z3::sort srt){
    vstring name = "c"+symbName;

    PRINT_CPP("{ sort s = sorts.back(); sorts.pop_back(); exprs.push_back(c.constant(\""<< name << "\",s)); }")

    return _context.constant(name.c_str(),srt);
  }


};

}//end SAT namespace

#endif /* if VZ3 */
#endif /*Z3Interfacing*/
