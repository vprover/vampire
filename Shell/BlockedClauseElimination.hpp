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

#include "Lib/Comparison.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Int.hpp"

#include "Indexing/ClauseCodeTree.hpp"

namespace Shell {

using namespace Kernel;

/**
 * Class for performing first-order BCE.
 */
class BlockedClauseElimination
{
public:
  /**
   * Equational version of the tautologyhood check is weaker, but has to be used in the presence of positive equalities.
   *
   * The option forceEquationally forces this even if autodetect would safely not use the equational version.
   *
   * With useSubsumption, a resolvent which is not a tautology may still be discharged by being
   * subsumed by another clause of the current clause set; this only applies to the non-equational
   * check, where the resolvent under the mgu is an actual first-order resolvent.
  */
  BlockedClauseElimination(bool forceEquationally = false, bool useSubsumption = false)
    : _forceEquationally(forceEquationally), _useSubsumption(useSubsumption) {}

  void apply(Kernel::Problem& prb);

private:
  bool _forceEquationally;
  bool _useSubsumption;

  struct ClWrapper;

  struct Candidate {
    USE_ALLOCATOR(Candidate);

    Candidate(ClWrapper* clw, unsigned litIdx) : clw(clw), litIdx(litIdx), contFrom(0), weight(0) {}

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
    USE_ALLOCATOR(ClWrapper);

    Clause* cl;            // the actual clause
    bool blocked;          // if already blocked, don't need to try again
    bool indexed;          // whether cl made it into _ct (and thus needs removing on blocking)
    Stack<Candidate*> toResurrect; // when getting block (effectively deleted, all these have a chance again)

    ClWrapper(Clause* cl) : cl(cl), blocked(false), indexed(false) {}
  };

  /**
   * Does @b partner fail to prevent @b cand's clause from being blocked?
   *
   * Either the resolvent is a tautology, or -- with _useSubsumption -- it is subsumed by another
   * clause of the current clause set, which is then reported via @b bySubsumption.
   */
  bool clearedBy(bool equationally, Kernel::RobSubstitution& subst, Candidate* cand, Candidate* partner, bool& bySubsumption);

  bool resolvesToTautology(bool equationally, Kernel::RobSubstitution& subst, Clause* cl, Literal* lit, Clause* pcl, Literal* plit);

  bool resolvesToTautologyUn(Kernel::RobSubstitution& subst, Clause* cl, Literal* lit, Clause* pcl, Literal* plit);

  bool resolvesToTautologyEq(Clause* cl, Literal* lit, Clause* pcl, Literal* plit);

  // the below are only used with _useSubsumption

  /**
   * The resolvent of cl (on its litIdx-th literal) and pcl (on its plitIdx-th one) under the mgu
   * left in @b subst by resolvesToTautologyUn, deduplicated. Returns 0 either when the resolvent
   * turns out to be a tautology after all (then @b tautology is set) or when it is empty.
   * The caller owns the returned clause and is expected to destroy() it.
   */
  Kernel::Clause* buildResolvent(Kernel::RobSubstitution& subst, Clause* cl, unsigned litIdx, Clause* pcl, unsigned plitIdx, bool& tautology);

  /** Is @b resolvent subsumed by a clause of the index other than @b exclude? */
  bool subsumedBy(Kernel::Clause* resolvent, Kernel::Clause* exclude);

  void indexInsert(ClWrapper* clw);
  void indexRemove(ClWrapper* clw);

  Indexing::ClauseCodeTree<false> _ct;
  Lib::DHSet<Kernel::Clause*> _indexed;
};

};

#endif /* __BlockedClauseElimination__ */
