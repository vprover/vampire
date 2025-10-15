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
 * @file EtaNormaliser.cpp
 */

#include "Kernel/HOL/EtaNormaliser.hpp"

#include "SubtermReplacer.hpp"
#include "Kernel/HOL/TermShifter.hpp"
#include "Kernel/HOL/HOL.hpp"

TermList EtaNormaliser::normalise(TermList t) {
  if (t.isVar() || !t.term()->hasLambda())
    return t;

  if (t.isLambdaTerm()) {
    TermStack lambdaSorts;
    TermList matrix;
    HOL::getMatrixAndPrefSorts(t, matrix, lambdaSorts);

    if (matrix.isVar())
      return t; // ^^^^^^X can't eta reduce this

    TermList matrixSort = SortHelper::getResultSort(matrix.term());
    TermList reduced = normalise(matrix);

    if (reduced != matrix)
      t = HOL::create::surroundWithLambdas(reduced, lambdaSorts, matrixSort, true);

    return transformSubterm(t);
  }

  // t is not a lambda term

  TermList head;
  TermList headSort;
  TermStack args;
  TermStack argsModified;
  HOL::getHeadSortAndArgs(t, head, headSort, args);

  bool changed = false;
  for (unsigned j = 0; j < args.size(); j++) {
    argsModified.push(normalise(args[j]));
    changed = changed || (argsModified[j] != args[j]);
  }

  if (!changed)
    return t;

  return HOL::create::app(headSort, head, argsModified);
}

// uses algorithm for eta-reduction that can be found here:
// https://matryoshka-project.github.io/pubs/lambdae.pdf

TermList EtaNormaliser::transformSubterm(TermList t) {
  TermList body = t;
  int l = 0; // number of lambda binders
  while (body.isLambdaTerm()) {
    l++;
    body = body.lambdaBody();
  }

  if (l == 0)
    return t; //not a lambda term, cannot eta reduce

  int n = 0; // number of De bruijn indices at end of term
  TermList newBody = body;
  while (body.isApplication()) {
    auto dbIndex = body.rhs().deBruijnIndex();
    if (!dbIndex.isSome() || dbIndex.unwrap() != n)
      break;

    body = body.lhs();
    ++n;
  }

  auto mfi = TermShifter::shift(body, 0).second;
  int j = mfi.unwrapOr(INT_MAX); // j is minimum free index
  int k = std::min({l, n, j});

  if (k == 0)
    return t;

  for (unsigned i = 0; i < k; i++)
    newBody = newBody.lhs();

  newBody = TermShifter::shift(newBody, 0 - k).first;

  body = t;
  for (unsigned i = 0; i < l - k; i++)
    body = body.lambdaBody();


  // TermTransform doesn't work at top level...
  if (body == t)
    return newBody;

  return SubtermReplacer(body, newBody).replace(t);
}