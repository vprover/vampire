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

#include "Lib/Stack.hpp"
#include "Inferences/DemodulationHelper.hpp"

#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Indexing;

class ConditionalRedundancyHandler
{
public:
  static ConditionalRedundancyHandler* create(const Options& opts, const Ordering* ord);
  static void destroyClauseData(Clause* cl);

  virtual ~ConditionalRedundancyHandler() = default;

  virtual bool checkSuperposition(
    Clause* eqClause, Clause* rwClause, bool eqIsResult, ResultSubstitution* subs) const = 0;

  virtual void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const = 0;

  virtual bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const = 0;

  virtual bool handleReductiveUnaryInference(Clause* premise, RobSubstitution* subs) const = 0;

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
  ConditionalRedundancyHandlerImpl() = default;
  ConditionalRedundancyHandlerImpl(const Options& opts, const Ordering* ord)
    : _ord(ord), _demodulationHelper(opts,ord) {}

  /** Returns false if superposition should be skipped. */
  bool checkSuperposition(
    Clause* eqClause, Clause* rwClause, bool eqIsResult, ResultSubstitution* subs) const override;

  void insertSuperposition(
    Clause* eqClause, Clause* rwClause, TermList rwTermS, TermList tgtTermS, TermList eqLHS,
    Literal* rwLitS, Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const override;

  /** Returns false if resolution should be skipped. */
  bool handleResolution(
    Clause* queryCl, Literal* queryLit, Clause* resultCl, Literal* resultLit, ResultSubstitution* subs) const override;

  /** Returns false if inference should be skipped. */
  bool handleReductiveUnaryInference(Clause* premise, RobSubstitution* subs) const override;

private:
  const Ordering* _ord;
  Inferences::DemodulationHelper _demodulationHelper;
};

};

#endif // __ConditionalRedundancyHandler__
