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
 * @file PartialRedundancyHandler.hpp
 * Partial redundancy is based on the following ideas:
 * - For any generating inference, let's denote with F the conditions under
 *   which the inference is simplifying, i.e. under these conditions the
 *   main premise is made redundant by the conclusion and the side premise.
 *   For example, consider superposition left:
 * 
 *          l = r \/ C               s[l'] != t \/ D
 *          ---------------------------------------- σ = mgu(l,l')
 *                   (s[r] != t \/ C \/ D)σ
 * 
 *   The conditions F under which s[l'] != t \/ D is redundant are roughly
 *   l = l' /\ lσ > rσ /\ s[r]σ > tσ /\ (l = r)σ > Cσ /\ (s[l'] != t)σ > Dσ /\ Cσ.
 * 
 * - We work with constrained clauses C[G] and after performing a generating
 *   inference, we create a variant C[G /\ ~F] of the main premise and remove
 *   the original if C[G /\ ~F] has strictly less instances than C[G].
 * 
 * - Let's consider an inference on C[G] which is simplifying under condition F.
 *   If we find that G -> ~F (or equivalently G /\ F) is unsatisfiable, the
 *   instance of clause C is already redundant under these conditions, and we
 *   may skip the inference.
 * 
 * - Finally, we can store stronger (sufficient) conditions and check weaker
 *   (necessary) conditions if checking the full conditions is computationally
 *   expensive. Currently, we use (i) unification, (ii) ordering, (iii) AVATAR
 *   and (iv) literal constraints. By default, we use only unification constraints.
 */

#ifndef __PartialRedundancyHandler__
#define __PartialRedundancyHandler__

#include "Forwards.hpp"

#include "Kernel/Ordering.hpp"
#include "Kernel/TermPartialOrdering.hpp"

#include "Lib/Stack.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Indexing;

using OrderingConstraints = Stack<TermOrderingConstraint>;

struct PartialRedundancyEntry {
  OrderingConstraints ordCons;
  ClauseStack cls;
};

struct EntryContainer {
  TermOrderingDiagramUP tod;
  Stack<PartialRedundancyEntry*> entries;
};

class PartialRedundancyHandler
{
public:
  PartialRedundancyHandler(const Options& opts, const Ordering* ord)
    : _redundancyCheck(opts.demodulationRedundancyCheck() != Options::DemodulationRedundancyCheck::OFF),
      _encompassing(opts.demodulationRedundancyCheck() == Options::DemodulationRedundancyCheck::ENCOMPASS),
      _ord(ord) {}

  /** Returns false if superposition should be skipped. */
  bool checkSuperposition(
    Clause* eqClause, Clause* rwClause, ResultSubstitution* subs,
    Literal* rwLitS, TermList rwTermS, TermList tgtTermS, Clause* resClause, DHSet<Clause*>& premiseSet) const;

  void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTerm, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, ResultSubstitution* subs, Clause* resClause) const;

  /** Returns false if resolution should be skipped. */
  bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs, Clause* resClause) const;

  void checkEquations(Clause* cl) const;

  static void destroyClauseData(Clause* cl);

private:
  bool compareWithSuperpositionPremise(
    Clause* rwCl, Literal* rwLitS, TermList rwTerm, TermList rwTermS, TermList tgtTermS, Clause* eqCl, TermList eqLHS, OrderingConstraints& cons) const;

  void tryInsert(Clause* into, ResultSubstitution* subs, bool result, Clause* cl, OrderingConstraints&& ordCons, Clause* res) const;

  class ConstraintIndex;

  static ConstraintIndex** getDataPtr(Clause* cl, bool doAllocate);

  // this contains the redundancy information associated with each clause
  static DHMap<Clause*,ConstraintIndex*> clauseData;

  bool _redundancyCheck;
  bool _encompassing;
  const Ordering* _ord;
};

};

#endif // __PartialRedundancyHandler__
