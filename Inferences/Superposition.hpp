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


#ifndef __Superposition__
#define __Superposition__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"
#include "Inferences/ProofExtra.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class Superposition
: public GeneratingInferenceEngine
{
public:
  Superposition(SaturationAlgorithm& salg);
  ClauseIterator generateClauses(Clause* premise) override;

private:
  Clause* performSuperposition(
    Clause* rwClause, Literal* rwLiteral, TermList rwTerm,
    Clause* eqClause, Literal* eqLiteral, TermList eqLHS,
    AbstractingUnifier* unifier, bool eqIsResult);

  bool checkClauseColorCompatibility(Clause* eqClause, Clause* rwClause);
  static bool checkSuperpositionFromVariable(Clause* eqClause, Literal* eqLit, TermList eqLHS);

  struct ForwardResultFn;

  struct LHSsFn;
  struct RewritableResultsFn;
  struct BackwardResultFn;

  SaturationAlgorithm& _salg;
  std::shared_ptr<SuperpositionSubtermIndex> _subtermIndex;
  std::shared_ptr<SuperpositionLHSIndex> _lhsIndex;
};

using SuperpositionExtra = TwoLiteralRewriteInferenceExtra;

};

#endif /* __Superposition__ */
