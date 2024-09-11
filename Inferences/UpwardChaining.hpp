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
 * @file UpwardChaining.hpp
 * Defines class UpwardChaining
 *
 */

#ifndef __UpwardChaining__
#define __UpwardChaining__

#include "Forwards.hpp"

#include "InferenceEngine.hpp"
#include "Induction.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/TermTransformer.hpp"

#include "Lib/ScopedPtr.hpp"
#include "Lib/SharedSet.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class UpwardChaining
: public GeneratingInferenceEngine
{
public:
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;

private:
  Clause* perform(
    Clause* rwClause, Literal* rwLit, TermList rwSide, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS, const Position& pos,
    ResultSubstitutionSP subst, bool eqIsResult, bool left);

  using TermIndex = TermIndex<TermLiteralClause>;

  TermIndex* _leftLhsIndex;
  TermIndex* _rightLhsIndex;
  TermIndex* _leftSubtermIndex;
  TermIndex* _rightSubtermIndex;
};

}

#endif /*__UpwardChaining__*/