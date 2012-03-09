/**
 * @file SimpleSMT.hpp
 * Defines class SimpleSMT.
 */

#ifndef __SimpleSMT__
#define __SimpleSMT__

#include "Forwards.hpp"
#include "Lib/DHMap.hpp"
#include "SAT/SATLiteral.hpp"
#include "Lib/Numbering.hpp"


namespace VUtils {

  using namespace Kernel;
  using namespace Shell;
  using namespace SAT;

  typedef Numbering<Literal *, 1 > TwoWayMap;

  class SimpleSMT {
  public:
    int perform(int argc, char** argv);
  protected:
    SAT::SATLiteral litTOSAT(Literal *l);
    void initializeSATSolver(ClauseIterator clite);
    LiteralStack getLiteralAssignmentStack();
    void preprocessProblem(int argc, char** argv);
    bool getCClosureClauseStatus(LiteralStack litAsgn);
  private: 
     //keeps a map between the literals found in the clauses and the SAT literals
    TwoWayMap _map;
    SAT::SATSolver *_solver;
  };
}

#endif // __SimpleSMT__
