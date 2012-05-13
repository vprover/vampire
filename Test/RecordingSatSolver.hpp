/**
 * @file RecordingSatSolver.hpp
 * Defines class RecordingSatSolver.
 */

#ifndef __RecordingSatSolver__
#define __RecordingSatSolver__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/OptionsReader.hpp"

#include "SAT/SATSolver.hpp"



namespace Test {

using namespace SAT;

class RecordingSatSolver : public SATSolver {
public:
  RecordingSatSolver(SATSolver* inner) : _inner(inner) {}

  virtual void addClauses(SATClauseIterator cit, bool onlyPropagate);
  virtual void randomizeAssignment();
  virtual void ensureVarCnt(unsigned newVarCnt);
  virtual void addAssumption(SATLiteral lit, unsigned conflictCountLimit);
  virtual void retractAllAssumptions();

  virtual Status getStatus() { return _inner->getStatus(); }
  virtual VarAssignment getAssignment(unsigned var) { return _inner->getAssignment(var); }
  virtual bool isZeroImplied(unsigned var) { return _inner->isZeroImplied(var); }
  virtual void collectZeroImplied(SATLiteralStack& acc) { return _inner->collectZeroImplied(acc); }
  virtual SATClause* getZeroImpliedCertificate(unsigned var) { return _inner->getZeroImpliedCertificate(var); }
  virtual bool hasAssumptions() const { return _inner->hasAssumptions(); }
  virtual SATClause* getRefutation() { return _inner->getRefutation(); }

private:

  string getHdr() const;

  SATSolverSCP _inner;
};


class SolverReplayer {
public:
  SolverReplayer(SATSolver& solver) : _solver(solver) {}

  enum ReplayAction {
    RA_ADD_CLAUSES,
    RA_ADD_ASSUMPTION,
    RA_RANDOMIZE_ASSIGNMENT,
    RA_ENSURE_VAR_CNT,
    RA_RETRACT_ALL_ASSUMPTIONS
  };

  static const EnumReader<ReplayAction>& getReplayActionReader();
  struct ActionSpec {
    ActionSpec();

    ReplayAction action;
    unsigned acOnlyPropagate;
    string acClausesStr;
    SATClauseStack acClauses;
    unsigned evcVarCnt;
    unsigned aaLitVar;
    unsigned aaLitPolarity;
    SATLiteral aaLit;
    unsigned aaConflictCountLimit;

    OptionsReader rdr;


    void readCommand(string str);

    SATClauseIterator getClauses() {
      ASS_EQ(action, RA_ADD_CLAUSES);
      return pvi(SATClauseStack::BottomFirstIterator(acClauses));
    }
  private:
    SATClause* readClause(string str);
  };

  void performStep(string cmd);
  void runFromStream(istream& stm, string prefix);

private:
  SATSolver& _solver;
};

}

#endif // __RecordingSatSolver__
