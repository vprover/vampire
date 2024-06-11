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
 * @file InstanceRedundancyHandler.hpp
 * Defines class InstanceRedundancyHandler.
 */

#ifndef __InstanceRedundancyHandler__
#define __InstanceRedundancyHandler__

#include "Forwards.hpp"

#include "Lib/Stack.hpp"
#include "Inferences/DemodulationHelper.hpp"

#include "Options.hpp"

namespace Indexing {

using namespace Inferences;
using namespace Lib;
using namespace Shell;

class InstanceRedundancyHandler
{
public:
  InstanceRedundancyHandler() = default;
  InstanceRedundancyHandler(const Options& opts, const Ordering* ord)
    : _optVal(opts.instanceRedundancyCheck()), _ord(ord), _demodulationHelper(opts,ord) {}

  /** Returns false if superposition should be skipped. */
  bool handleSuperposition(
    Clause* eqClause, Clause* rwClause,
    TermList rwTermS, TermList tgtTermS, TermList eqLHS, Literal* rwLitS,
    Ordering::Result eqComp, bool eqIsResult, ResultSubstitution* subs) const;

  /** Returns false if resolution should be skipped. */
  static bool handleResolution(
    Clause* queryCl, Literal* queryLit,
    Clause* resultCl, Literal* resultLit,
    ResultSubstitution* subs, const Options& opts, const Ordering* ord);

  /** Returns false if inference should be skipped. */
  static bool handleReductiveUnaryInference(
    Clause* premise, RobSubstitution* subs, const Ordering* ord);

  static void destroyClauseData(Clause* cl);

private:
  Options::InstanceRedundancyCheck _optVal;
  const Ordering* _ord;
  Inferences::DemodulationHelper _demodulationHelper;
};

};

#endif // __InstanceRedundancyHandler__
