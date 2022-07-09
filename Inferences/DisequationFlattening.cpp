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

Kernel::ClauseIterator Inferences::DisequationFlattening::generateClauses(Clause *cl)
{
  static Stack<Clause *> results;
  static Stack<Literal *> out;

  results.reset();
  auto selected = cl->getSelectedLiteralIterator();
  while(selected.hasNext()) {
    Literal *l = selected.next();
    if (l->isPositive() || !l->isEquality() || l->isTwoVarEquality())
      continue;

    TermList ltl = *l->nthArgument(0);
    TermList rtl = *l->nthArgument(1);
    if (!TermList::sameTopFunctor(ltl, rtl))
      continue;
    Term *lt = ltl.term();
    Term *rt = rtl.term();

    // applying to polymorphic functions could create ill-typed terms
    // consider f: !>[X: $tType]: X > $i, a: t, b: s and
    // f(t, a) != f(s, b)
    // producing a != b
    if(lt->numTypeArguments())
      continue;

    out.reset();
    for (unsigned i = 0; i < cl->length(); i++)
      if(cl->literals()[i] != l)
        out.push(cl->literals()[i]);

    // NB no polymorphism
    for (unsigned i = 0; i < lt->arity(); i++)
      out.push(Literal::createEquality(
          false,
          *lt->nthArgument(i),
          *rt->nthArgument(i),
          SortHelper::getArgSort(lt, i)));

    Clause *result = Clause::fromStack(
        out,
        SimplifyingInference1(InferenceRule::DISEQUATION_FLATTENING, cl));
    results.push(result);
  }

  return pvi(results.iter());
}
