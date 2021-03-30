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
 * @file BlockedClauseElimination.hpp
 * Defines class BlockedClauseElimination.
 */


#ifndef __BlockedClauseElimination__
#define __BlockedClauseElimination__

#include "Forwards.hpp"

#include "Kernel/Problem.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Stack.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Class for performing first-order BCE.
 */
class BlockedClauseElimination
{
public:
  void apply(Kernel::Problem& prb);

private:
  struct ClWrapper;

  struct Candidate {
    CLASS_NAME(BlockedClauseElimination::Candidate);
    USE_ALLOCATOR(Candidate);

    ClWrapper* clw;
    unsigned litIdx;    // index of the potentially blocking literal L
    unsigned contFrom;  // index of the next resolution partner to try in op(L)'s list
    unsigned weight;    // how many resolution partners still need to be tested -- used to order the priority queue on
  };

  struct CandidateComparator {
    static Comparison compare(Candidate* c1, Candidate* c2) {
      return Int::compare(c1->weight,c2->weight);
    }
  };

  struct ClWrapper {
    CLASS_NAME(BlockedClauseElimination::ClWrapper);
    USE_ALLOCATOR(ClWrapper);

    Clause* cl;            // the actual clause
    bool blocked;          // if already blocked, don't need to try again
    Stack<Candidate*> toResurrect; // when getting block (effectively deleted, all these have a chance again)

    ClWrapper(Clause* cl) : cl(cl), blocked(false) {}
  };

  bool resolvesToTautology(bool equationally, Clause* cl, Literal* lit, Clause* pcl, Literal* plit);

  bool resolvesToTautologyUn(Clause* cl, Literal* lit, Clause* pcl, Literal* plit);

  bool resolvesToTautologyEq(Clause* cl, Literal* lit, Clause* pcl, Literal* plit);
};

};

#endif /* __BlockedClauseElimination__ */
