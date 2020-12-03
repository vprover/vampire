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
 * @file FnDefSuperposition.hpp
 * Defines class FnDefSuperposition.
 */


#ifndef __FnDefSuperposition__
#define __FnDefSuperposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FnDefSuperposition
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(FnDefSuperposition);
  USE_ALLOCATOR(FnDefSuperposition);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise) override;

private:
  Clause* performSuperposition(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
	  ResultSubstitutionSP subst, bool eqIsResult,
    UnificationConstraintStackSP constraints);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct UnificationsFn;
  struct BackwardResultFn;

  SuperpositionSubtermIndex* _subtermIndex;
  FnDefLHSIndex* _lhsIndex;
};


};

#endif /* __Superposition__ */
