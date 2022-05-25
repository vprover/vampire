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
 * @file SubVarSup.hpp
 * Defines class SubVarSup.
 */


#ifndef __SubVarSup__
#define __SubVarSup__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class SubVarSup
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(SubVarSup);
  USE_ALLOCATOR(SubVarSup);

  void attach(SaturationAlgorithm* salg);
  void detach();

  ClauseIterator generateClauses(Clause* premise);


private:
  Clause* performSubVarSup(
	  Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
	  Clause* eqClause, Literal* eqLiteral, TermList eqLHS, bool eqIsResult);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct ApplicableRewritesFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  SubVarSupSubtermIndex* _subtermIndex;
  SubVarSupLHSIndex* _lhsIndex;
};


};

#endif /* __SubVarSup__ */
