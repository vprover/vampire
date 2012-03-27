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

#include "SAT/SATLiteral.hpp"
#include "SAT/SATSolver.hpp"

namespace VUtils {

using namespace Kernel;
using namespace Shell;
using namespace SAT;

class SimpleSMT {
  public:
    int perform(int argc, char** argv);
    SimpleSMT(){};
    ~SimpleSMT(){};
  protected:
    void initializeSATSolver(ClauseIterator clite);
    void getLiteralAssignmentStack(LiteralStack *litAsgn);
    void preprocessProblem(int argc, char** argv);
    void initSATSolver(SATClauseIterator clauseIterator);
    void addClauseToSAT(SATClause *clause);
    unsigned getCClosureClauseStatus(LiteralStack *litAsgn);
    unsigned compute();
    SATClauseIterator initSATClauses(ClauseIterator clite);
    SATLiteral litTOSAT(Literal *l); 
    SATClause* convertSATtoFO(LiteralStack *litAsgn);
    
  private:
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
