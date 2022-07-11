/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Forwards.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

#include "DisequationFlattening.hpp"

using Kernel::Clause;

Inferences::DisequationFlattening::~DisequationFlattening() {}

bool Inferences::DisequationFlattening::eligibleForFlattening(Literal *l)
{
  CALL("DisequationFlattening::eligibleForFlattening");
  if (l->isPositive() || !l->isEquality())
    return false;

  TermList left = *l->nthArgument(0);
  TermList right = *l->nthArgument(1);
  if (!TermList::sameTopFunctor(left, right))
    return false;

  // applying to polymorphic functions could create ill-typed terms
  // consider f: !>[X: $tType]: X > $i, a: t, b: s and
  // f(t, a) != f(s, b)
  // producing a != b
  if(left.term()->numTypeArguments())
    return false;

  return true;
}

Kernel::ClauseIterator Inferences::DisequationFlattening::generateClauses(Clause *cl)
{
  CALL("DisequationFlattening::generateClauses");
  static Stack<Clause *> results;
  static Stack<Literal *> out;

  results.reset();
  auto selected = cl->getSelectedLiteralIterator();
  while(selected.hasNext()) {
    Literal *l = selected.next();
    if(!eligibleForFlattening(l))
      continue;

    // guaranteed to be of the form f(...) != f(...) since eligibleForFlattening
    Term *left = l->nthArgument(0)->term();
    Term *right = l->nthArgument(1)->term();

    out.reset();
    for (unsigned i = 0; i < cl->length(); i++)
      if(cl->literals()[i] != l)
        out.push(cl->literals()[i]);

    // NB no polymorphism since eligibleForFlattening
    for (unsigned i = 0; i < left->arity(); i++)
      out.push(Literal::createEquality(
          false,
          *left->nthArgument(i),
          *right->nthArgument(i),
          SortHelper::getArgSort(left, i)));

    Clause *result = Clause::fromStack(
        out,
        SimplifyingInference1(InferenceRule::DISEQUATION_FLATTENING, cl));
    results.push(result);
  }

  return pvi(results.iter());
}
