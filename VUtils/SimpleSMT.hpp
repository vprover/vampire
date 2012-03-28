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
    SimpleSMT() : _conflictIndex(0) {};
    ~SimpleSMT(){};
  protected:
    void initializeSATSolver(ClauseIterator clite);
    void getLiteralAssignmentStack(LiteralStack& litAsgn);
    void preprocessProblem(int argc, char** argv);
    void initSATSolver(SATClauseIterator clauseIterator);
    void addClausesToSAT(SATClauseStack& clauses);
    DecisionProcedure::Status addTheoryConflicts(LiteralStack& assignment);
    DecisionProcedure::Status compute();
    SATClauseIterator initSATClauses(ClauseIterator clite);
    SATLiteral litTOSAT(Literal *l); 
    SATClause* convertSATtoFO(LiteralStack *litAsgn);
    
  private:
    unsigned _conflictIndex;

    typedef Numbering<Literal *, 1 > TwoWayMap;
     /**
      * keeps a map between the literals found in the clauses and the SAT literals
      */
    TwoWayMap _map;
    //### (1) memory leak, one can deallocate in the destructor (as long as you assign to zero in constructor)
    //###     but the use of ScopedPtr would be even better
    ScopedPtr<SATSolver> _solver;
    //SATSolver* _solver;
};

}

#endif // __SimpleSMT__
