
/*
 * File SimpleSMT.hpp.
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

/**
 * A simple SMT solver call: read a problem from the input file or stdin, solve
 * it and print the result (satisfiable, unsatisfiable or unknown). 
 */
class SimpleSMT {
public:
  int perform(int argc, char** argv);
  SimpleSMT();
  ~SimpleSMT(){};
private:
  void initializeSATSolver(ClauseIterator clite);
  void preprocessProblem(int argc, char** argv);
  void initSATSolver(SATClauseIterator clauseIterator);
  void addClausesToSAT(SATClauseStack& clauses);
  DecisionProcedure::Status addTheoryConflicts(LiteralStack& assignment);
  DecisionProcedure::Status compute();
  SATClauseIterator initSATClauses(ClauseIterator clite);
  SATClause* convertSATtoFO(LiteralStack *litAsgn);
  
  unsigned _conflictIndex;
  SAT2FO _map;
  ScopedPtr<SATSolver> _solver;
  ScopedPtr<DecisionProcedure> _dp;
}; // simpleSMT

}

#endif // __SimpleSMT__
