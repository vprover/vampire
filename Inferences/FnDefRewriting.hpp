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
 * @file FnDefRewriting.hpp
 * Defines class FnDefRewriting.
 */


#ifndef __FnDefRewriting__
#define __FnDefRewriting__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class FnDefRewriting
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(FnDefRewriting);
  USE_ALLOCATOR(FnDefRewriting);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise) override;

private:
  static Clause* perform(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
	  ResultSubstitutionSP subst, bool eqIsResult);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct InstancesFn;
  struct GeneralizationsFn;
  struct BackwardResultFn;

  DemodulationSubtermIndex* _subtermIndex;
  FnDefLHSIndex* _lhsIndex;
};


};

#endif /* __FnDefRewriting__ */
