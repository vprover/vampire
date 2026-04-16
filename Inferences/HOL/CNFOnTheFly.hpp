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
 * @file ProxyElimination.hpp
 * Defines class ProxyElimination.
 */

#ifndef __CNFOnTheFly__
#define __CNFOnTheFly__

#include "Forwards.hpp"
#include "Inferences/InferenceEngine.hpp"

#include "Indexing/TermIndex.hpp"

namespace Inferences {
using namespace Indexing;

class IFFXORRewriterISE
  : public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* c) override;
};

class EagerClausificationISE
  : public ImmediateSimplificationEngineMany
{
public:
  Option<ClauseIterator> simplifyMany(Clause* c) override;
};

class LazyClausification
  : public SimplificationEngine
{
public:
  LazyClausification(SaturationAlgorithm& salg);

  ClauseIterator perform(Clause* c) override;
private:
  std::shared_ptr<SkolemisingFormulaIndex> _formulaIndex;
};

class LazyClausificationGIE
  : public GeneratingInferenceEngine
{
public:
  LazyClausificationGIE(SaturationAlgorithm& salg);
  ClauseIterator generateClauses(Clause* c) override;

private:
  std::shared_ptr<SkolemisingFormulaIndex> _formulaIndex;
};

}

#endif
