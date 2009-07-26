/**
 * @file DIMACS.hpp
 * Defines class DIMACS.
 */

#ifndef __DIMACS__
#define __DIMACS__

#include "../Lib/VirtualIterator.hpp"

#include "SATClause.hpp"

namespace SAT
{

class DIMACS
{
public:
  static SATClauseIterator parse(const char* fname, unsigned& maxVar);

  static void outputProblem(SATClauseList* clauses, ostream& out);
};

}

#endif /* __DIMACS__ */
