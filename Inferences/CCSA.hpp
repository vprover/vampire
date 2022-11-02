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
    TermList relation,
    TermList subterm,
    TermList subterm_sort,
    TermList superterm,
    TermList superterm_sort
  );

  static void registerCommutes(unsigned relation, unsigned functor);
};

class RewriteGIE : public GeneratingInferenceEngine
{
public:
  CLASS_NAME(RewriteISE);
  USE_ALLOCATOR(RewriteGIE);
  ClauseIterator generateClauses(Clause* cl) override;

  static void registerTermRewrite(TermList left, TermList right);
  static void registerLiteralRewrite(Literal *left, Literal *right);
};

}
