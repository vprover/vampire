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

#include "Lib/Stack.hpp"
#include "Lib/SharedSet.hpp"

#include "Saturation/Splitter.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Indexing;

using LiteralSet = Set<Literal*,SharedTermHash>;

using OrderingConstraints = Stack<TermOrderingConstraint>;

struct PartialRedundancyEntry {
  OrderingConstraints ordCons;
  LiteralSet lits;
  SplitSet* splits;
  bool active = true;
  unsigned refcnt = 1;

  void deactivate() {
    ASS(!splits->isEmpty());
    active = false;
  }

  void obtain() {
    refcnt++;
  }

  void release() {
    ASS(refcnt);
    refcnt--;
    if (!refcnt) {
      delete this;
    }
  }
};

struct EntryContainer {
  TermOrderingDiagramUP tod;
  Stack<PartialRedundancyEntry*> entries;
};

class PartialRedundancyHandler
{
public:
  static PartialRedundancyHandler* create(const Options& opts, const Ordering* ord, Splitter* splitter);
  static void destroyClauseData(Clause* cl);

  virtual ~PartialRedundancyHandler() = default;

  virtual bool checkSuperposition(
    Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit, bool eqIsResult, ResultSubstitution* subs) const = 0;

  virtual void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTerm, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const = 0;

  virtual bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const = 0;

  virtual void checkEquations(Clause* cl) const = 0;

protected:
  class ConstraintIndex;

  static ConstraintIndex** getDataPtr(Clause* cl, bool doAllocate);

  // this contains the redundancy information associated with each clause
  static DHMap<Clause*,ConstraintIndex*> clauseData;
};

template<bool enabled, bool orderingConstraints, bool avatarConstraints, bool literalConstraints>
class PartialRedundancyHandlerImpl
  : public PartialRedundancyHandler
{
public:
  PartialRedundancyHandlerImpl(const Options& opts, const Ordering* ord, Splitter* splitter)
    : _redundancyCheck(opts.demodulationRedundancyCheck() != Options::DemodulationRedundancyCheck::OFF),
      _encompassing(opts.demodulationRedundancyCheck() == Options::DemodulationRedundancyCheck::ENCOMPASS),
      _ord(ord), _splitter(splitter) {}

  /** Returns false if superposition should be skipped. */
  bool checkSuperposition(
    Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit, bool eqIsResult, ResultSubstitution* subs) const override;

  void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTerm, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const override;

  /** Returns false if resolution should be skipped. */
  bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const override;

  void checkEquations(Clause* cl) const override;

private:
  bool compareWithSuperpositionPremise(
    Clause* rwCl, Literal* rwLitS, TermList rwTerm, TermList rwTermS, TermList tgtTermS, Clause* eqCl, TermList eqLHS, OrderingConstraints& cons) const;

  LiteralSet getRemainingLiterals(Clause* cl, Literal* lit, ResultSubstitution* subs, bool result) const;

  const SplitSet* getRemainingSplits(Clause* cl, Clause* other) const;
  void tryInsert(Clause* into, ResultSubstitution* subs, bool result, Clause* cl, OrderingConstraints&& ordCons,
    LiteralSet&& lits, SplitSet* splits) const;

  bool _redundancyCheck;
  bool _encompassing;
  const Ordering* _ord;
  Splitter* _splitter;
};

};

#endif // __PartialRedundancyHandler__
