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
 * @file Superposition.hpp
 * Defines class Superposition.
 */


#ifndef __Narrow__
#define __Narrow__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Narrow
: public GeneratingInferenceEngine
{
public:
  ClauseIterator generateClauses(Clause* premise) override;

  /** TODO 2 should we make this a correct estimation */
  virtual VirtualIterator<std::tuple<>> lookaheadResultEstimation(SelectedAtom const& selection) override
  { return pvi(dropElementType(range(0,0))); }

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

private:
  NarrowingIndex* _index;

  Clause* performNarrow(
    Clause* nClause, Literal* nLiteral, TermList nTerm, 
    TermList combAxLhs, Literal* combAx, ResultSubstitutionSP subst);
 
  struct ApplicableNarrowsFn;
  struct RewriteableSubtermsFn;
  struct ResultFn;

};


};

#endif /* __Narrow__ */
