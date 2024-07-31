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
 * @file ConditionalRedundancyHandler.hpp
 * Defines class ConditionalRedundancyHandler.
 */

#ifndef __ConditionalRedundancyHandler__
#define __ConditionalRedundancyHandler__

#include "Forwards.hpp"

#include "Kernel/Ordering.hpp"

#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

#include "Inferences/DemodulationHelper.hpp"

#include "Saturation/Splitter.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Indexing;

using LiteralSet = SharedSet<Literal*>;

struct ConditionalRedundancyEntry {
  Term* lhs;
  Term* rhs;
  OrderingComparatorUP comp;
  const LiteralSet* lits;
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

class ConditionalRedundancyHandler
{
public:
  static ConditionalRedundancyHandler* create(const Options& opts, const Ordering* ord, Splitter* splitter);
  static void destroyClauseData(Clause* cl);

  virtual ~ConditionalRedundancyHandler() = default;

  virtual bool checkSuperposition(
    Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit, bool eqIsResult, ResultSubstitution* subs) const = 0;

  virtual void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const = 0;

  virtual bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const = 0;

  virtual bool handleReductiveUnaryInference(Clause* premise, RobSubstitution* subs) const = 0;

  void checkEquations(Clause* cl) const;

protected:
  class SubstitutionCoverTree;

  static SubstitutionCoverTree** getDataPtr(Clause* cl, bool doAllocate);

  // this contains the redundancy information associated with each clause
  static DHMap<Clause*,SubstitutionCoverTree*> clauseData;
};

template<bool enabled, bool orderingConstraints, bool avatarConstraints, bool literalConstraints>
class ConditionalRedundancyHandlerImpl
  : public ConditionalRedundancyHandler
{
public:
  ConditionalRedundancyHandlerImpl(const Options& opts, const Ordering* ord, Splitter* splitter)
    : _ord(ord), _demodulationHelper(opts,ord), _splitter(splitter) {}

  /** Returns false if superposition should be skipped. */
  bool checkSuperposition(
    Clause* eqClause, Literal* eqLit, Clause* rwClause, Literal* rwLit, bool eqIsResult, ResultSubstitution* subs) const override;

  void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Literal* eqLit, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const override;

  /** Returns false if resolution should be skipped. */
  bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const override;

  /** Returns false if inference should be skipped. */
  bool handleReductiveUnaryInference(Clause* premise, RobSubstitution* subs) const override;

private:
  const Ordering* _ord;
  Inferences::DemodulationHelper _demodulationHelper;
  Splitter* _splitter;
};

};

#endif // __ConditionalRedundancyHandler__
