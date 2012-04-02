/**
 * @file SimpleSMT.hpp
 * Defines class SimpleSMT.
 */

#ifndef __SimpleSMT__
#define __SimpleSMT__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/Numbering.hpp"
#include "Lib/ScopedPtr.hpp"

#include "DP/DecisionProcedure.hpp"

#include "SAT/SAT2FO.hpp"
#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

namespace VUtils {

using namespace Kernel;
using namespace Shell;
using namespace SAT;
using namespace DP;

class SimpleSMT {
  public:
    int perform(int argc, char** argv);
    SimpleSMT();
    ~SimpleSMT(){};
  protected:
    void initializeSATSolver(ClauseIterator clite);
    void preprocessProblem(int argc, char** argv);
    void initSATSolver(SATClauseIterator clauseIterator);
    void addClausesToSAT(SATClauseStack& clauses);
    DecisionProcedure::Status addTheoryConflicts(LiteralStack& assignment);
    DecisionProcedure::Status compute();
    SATClauseIterator initSATClauses(ClauseIterator clite);
    SATClause* convertSATtoFO(LiteralStack *litAsgn);

  private:
    unsigned _conflictIndex;

    SAT2FO _map;

    ScopedPtr<SATSolver> _solver;
    ScopedPtr<DecisionProcedure> _dp;
};

}

#endif // __SimpleSMT__
