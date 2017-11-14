
/*
 * File DIMACS.hpp.
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
 * @file DIMACS.hpp
 * Defines class DIMACS.
 */

#ifndef __DIMACS__
#define __DIMACS__

#include "Forwards.hpp"
#include "Lib/VirtualIterator.hpp"

#include "SATClause.hpp"

namespace SAT
{

class DIMACS
{
public:
  static SATClauseList* parse(const char* fname, unsigned& maxVar);

  static void outputGroundedProblem(MapToLIFO<Clause*, SATClause*>& insts,
	  SATClause::NamingContext& nctx, ostream& out);
  static void outputProblem(SATClauseList* clauses, ostream& out);

private:
  static void getStats(SATClauseIterator clauses, unsigned& clauseCnt, unsigned& maxVar);
};

}

#endif /* __DIMACS__ */
