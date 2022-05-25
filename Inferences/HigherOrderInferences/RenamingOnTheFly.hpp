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

#ifndef __RenamingOnTheFly__
#define __RenamingOnTheFly__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Kernel/Inference.hpp"

#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"

namespace Inferences {
using namespace Indexing;


class RenamingOnTheFly
  : public SimplificationEngine
{
public:
  CLASS_NAME(RenamingOnTheFly);
  USE_ALLOCATOR(RenamingOnTheFly);

  ClauseIterator perform(Clause* c);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;

  //todo make an option
private:
  ClauseIterator produceClauses(Clause* c);
  void addToQueue(TermList formula, TermList name, Literal* lit, Clause* c);
  void processQueue();
  bool isNamingLit(Literal* lit);
  TermList getFormula(Literal* lit);

  TermStack _formulas;
  TermStack _names;
  LiteralStack _lits;
  ClauseStack _clauses;
  RenamingFormulaIndex* _formulaIndex;
};




}

#endif
