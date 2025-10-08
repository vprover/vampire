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
 * @file GoalRewriting.hpp
 * Defines class GoalRewriting
 *
 */

#ifndef __GoalRewriting__
#define __GoalRewriting__

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

using Position = Stack<unsigned>;

class GoalRewriting
: public GeneratingInferenceEngine
{
public:
  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;

private:
  Clause* perform(Clause* rwClause, Literal* rwLit, Term* rwSide, const Term* rwTerm, const Position& pos,
    Clause* eqClause, Literal* eqLit, TermList eqRhs, ResultSubstitution* subst, bool eqIsResult);

  TermIndex<TermLiteralClause>* _goalTermIndex;
  TermIndex<TermLiteralClause>* _rhsIndex;
  TermIndex<TermPositionSideLiteralClause>* _subtermIndex;
};

}

#endif /*__GoalRewriting__*/