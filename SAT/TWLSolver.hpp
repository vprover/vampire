/**
 * @file TWLSolver.hpp
 * Defines class TWLSolver of two-watched-literals SAT solver.
 */


#ifndef __TWLSolver__
#define __TWLSolver__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Stack.hpp"

namespace SAT {

using namespace Lib;

class TWLSolver {
public:
  enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    TIME_LIMIT
  };

  TWLSolver();

  void addClauses(SATClauseIterator cit);
  Status getStatus() { return _status; };
  void ensureVarCnt(unsigned newVarCnt);

  void assertValid();
  bool isFalse(SATClause* cl);
  void printAssignment();
private:

  void addClause(SATClause* cl);
  void addUnitClause(SATClause* cl);

  void addMissingWatchLitClause(SATClause* cl);

  void backtrack(unsigned tgtLevel);
  unsigned propagate(unsigned var);
  void incorporateUnprocessed();
  unsigned getBacktrackLevel(SATClause* conflictClause);

  void insertIntoWatchIndex(SATClause* cl);

  bool chooseVar(unsigned& var);

  enum AsgnVal {
    //the true and false value also correspond to positive
    //and negative literal polarity values
    AS_FALSE = 0u,
    AS_TRUE = 1u,
    AS_UNDEFINED = 2u
  };

  /** Unit-stack record */
  struct USRec
  {
    unsigned var;
    unsigned choice : 1;
    unsigned mark : 1;
    unsigned markedIsDefining : 1;
    unsigned markTgtLevel : 29;
    USRec() {}
    USRec(unsigned var, bool choice, bool mark=false,
	    bool markedIsDefining=false, unsigned markTgtLevel=0)
    : var(var), choice(choice), mark(mark), markedIsDefining(markedIsDefining),
    markTgtLevel(markTgtLevel)
    {}

  };


  Status _status;
  DArray<AsgnVal> _assignment;
  DArray<unsigned> _assignmentLevels;

  /**
   * If a clause was determined at a choice point, its entry
   * is 0, otherwise it's the Clause that led to the assignment
   * by unit propagation.
   */
  DArray<SATClause*> _assignmentPremises;

  /**
   * Stack of assignment records.
   */
  Stack<USRec> _unitStack;
  /**
   * The two-watched-literals index.
   *
   * Invariant: each clause is either true,
   * or it's two watched literals are undefined.
   */
  DArray<Stack<SATClause*> > _windex;

  /**
   * Clauses that aren't part of the _windex.
   *
   * These clauses can't be added until we backtrack to certain level.
   */
  DArray<Stack<SATClause*> > _unprocessed;

  ZIArray<unsigned> _chosenVars;

  unsigned _varCnt;

  /** Level 1 is the first level which is not preceded by any choice point */
  unsigned _level;

  class UnsatException : public Exception
  {};

};

}

#endif /* __TWLSolver__ */
