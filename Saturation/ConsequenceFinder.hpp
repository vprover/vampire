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
 * @file ConsequenceFinder.hpp
 * Defines class ConsequenceFinder for splitting with backtracking.
 */

#ifndef __ConsequenceFinder__
#define __ConsequenceFinder__

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Array.hpp"
#include "Lib/Event.hpp"
#include "Lib/Int.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"

#include "Inferences/TautologyDeletionISE.hpp"

namespace Saturation {

using namespace Kernel;
using namespace Inferences;

/**
 * The @b ConsequenceFinder object takes care of the
 * consequence-finding mode in Vampire
 */
class ConsequenceFinder {
public:
  ~ConsequenceFinder();

  void init(SaturationAlgorithm* sa);

  bool isRedundant(Clause* cl);

  void onNewPropositionalClause(Clause* cl);
  void onAllProcessed();

private:

  void onClauseInserted(Clause* cl);
  void onClauseRemoved(Clause* cl);

  void indexClause(unsigned indexNum, Clause* cl, bool add);

  SaturationAlgorithm* _sa;

  Lib::Stack<unsigned> _redundantsToHandle;

  typedef Lib::SkipList<Clause*,Lib::Int> ClauseSL;

  /** Index of clauses that contain specific consequence-finding
   * name predicate */
  Lib::ZIArray<ClauseSL*> _index;
  /** Keeps information on which claims have already been found
   * redundant (implied by others) */
  Lib::ZIArray<bool> _redundant;

  TautologyDeletionISE _td;
  DuplicateLiteralRemovalISE _dlr;

  /** SubscriptionData for the @b onClauseInserted method */
  Lib::SubscriptionData _sdInsertion;
  /** SubscriptionData for the @b onClauseRemoved method */
  Lib::SubscriptionData _sdRemoval;
};

}

#endif // __ConsequenceFinder__
