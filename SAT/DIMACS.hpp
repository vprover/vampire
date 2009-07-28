/**
 * @file DIMACS.hpp
 * Defines class DIMACS.
 */

#ifndef __DIMACS__
#define __DIMACS__

#include "../Forwards.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "SATClause.hpp"

namespace SAT
{

class DIMACS
{
public:
  static SATClauseIterator parse(const char* fname, unsigned& maxVar);

  static void outputGroundedProblem(MapToLIFO<Clause*, SATClause*>& insts,
	  SATClause::NamingContext& nctx, ostream& out);
  static void outputProblem(SATClauseList* clauses, ostream& out);

private:
  static void getStats(SATClauseIterator clauses, unsigned& clauseCnt, unsigned& maxVar);
};

}

#endif /* __DIMACS__ */
