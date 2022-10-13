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
 * @file Subterm.hpp
 * Inferences about a subterm relation
 */

#include "InferenceEngine.hpp"

namespace Inferences {

class SubtermGIE : public GeneratingInferenceEngine
{
public:
  CLASS_NAME(SubtermGIE);
  USE_ALLOCATOR(SubtermGIE);
  ClauseIterator generateClauses(Clause* premise) override;

  static Literal *createSubterm(
    bool polarity,
    TermList subterm,
    TermList subterm_sort,
    TermList superterm,
    TermList superterm_sort
  );
};

class RewriteISE : public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(RewriteISE);
  USE_ALLOCATOR(RewriteISE);
  Clause* simplify(Clause* cl) override;

  static void registerRewrite(Literal *rewrite);
};

}