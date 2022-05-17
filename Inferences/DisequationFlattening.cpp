/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "DisequationFlattening.hpp"

using Kernel::Clause;

Inferences::DisequationFlattening::~DisequationFlattening() {}

Indexing::ClauseIterator Inferences::DisequationFlattening::generateClauses(Clause *cl)
{
  static Stack<Clause *> results;
  static Stack<Literal *> out;

  results.reset();
  for (unsigned i = 0; i < cl->size(); i++) {
    Literal *l = cl->literals()[i];
    if (l->isPositive() || !l->isEquality() || l->isTwoVarEquality())
      continue;

    TermList ltl = *l->nthArgument(0);
    TermList rtl = *l->nthArgument(1);
    if (!TermList::sameTopFunctor(ltl, rtl))
      continue;

    out.reset();
    for (unsigned j = 0; j < i; j++)
      out.push(cl->literals()[j]);

    Term *lt = ltl.term();
    Term *rt = rtl.term();
    for (unsigned j = 0; j < lt->arity(); j++)
      out.push(Literal::createEquality(
          false,
          *lt->nthArgument(j),
          *rt->nthArgument(j),
          SortHelper::getArgSort(lt, j)));

    for (unsigned j = i + 1; j < cl->size(); j++)
      out.push(cl->literals()[j]);

    Clause *result = Clause::fromStack(
        out,
        SimplifyingInference1(InferenceRule::DISEQUATION_FLATTENING, cl));
    results.push(result);
  }

  return pvi(results.iter());
}