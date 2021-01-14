/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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
  static void outputGroundedProblem(MapToLIFO<Clause*, SATClause*>& insts,
	  SATClause::NamingContext& nctx, ostream& out);

private:
  static void getStats(SATClauseIterator clauses, unsigned& clauseCnt, unsigned& maxVar);
};

}

#endif /* __DIMACS__ */
