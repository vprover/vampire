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
 * @file FOOLParamodulation.cpp
 * Implements the inference rule, that is needed for efficient treatment of
 * boolean terms. The details of why it is needed are in the paper
 * "A First Class Boolean Sort in First-Order Theorem Proving and TPTP"
 * by Kotelnikov, Kovacs and Voronkov [1].
 *
 * [1] http://arxiv.org/abs/1505.01682
 */

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"

#include "FOOLParamodulation.hpp"

namespace Inferences {

ClauseIterator FOOLParamodulation::generateClauses(Clause* premise) {
  CALL("FOOLParamodulation::generateClauses");

  /**
   * We are going to implement the following inference rule, taken from the paper:
   *
   *        C[s]
   * --------------------, where
   * C[true] \/ s = false
   *
   * (a) s is a boolean term other than true or false;
   * (b) s is not a variable;
   * (c) C[s] is different from s = false.
   *
   * C[s] is a clause with an occurrence of s, and C[true] is the C clause
   * with s substituted by true.
   *
   * C[s] is deleted after the inference is applied.
   */

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  /**
   * We will be looking for a literal, standing in a `literalPosition` in
   * the clause, that has an occurrence of a `booleanTerm`, that is not a
   * variable, true or false.
   *
   * We will only be looking for one boolean term and only replace one
   * occurrence of it in one literal. An alternative implementation can:
   *  1) Replace all occurrences of a boolean term in all literals.
   *  2) Find occurrences of multiple boolean terms and replace their
   *     occurrences simultaneously, adding multiple literals of the form
   *     s_n = false to the conclusion.
   */
  TermList booleanTerm;
  unsigned literalPosition = 0;

  ArrayishObjectIterator<Clause> literals = premise->getSelectedLiteralIterator();
  while (literals.hasNext()) {
    Literal* literal = literals.next();

    // we shouldn't touch literals of the form s = false
    if (literal->isEquality() && literal->polarity()) {
      TermList* lhs = literal->nthArgument(0);
      TermList* rhs = literal->nthArgument(1);
      if ((lhs->isTerm() && env.signature->isFoolConstantSymbol(false,lhs->term()->functor())) ||
          (rhs->isTerm() && env.signature->isFoolConstantSymbol(false,rhs->term()->functor()))) {
        literalPosition++;
        continue;
      }
    }

    // we shouldn't replace variables, hence NonVariableIterator
    NonVariableIterator nvi(literal);
    while (nvi.hasNext()) {
      TermList subterm = nvi.next();
      unsigned functor = subterm.term()->functor();

      // we shouldn't replace boolean constants
      if (env.signature->isFoolConstantSymbol(false,functor) || env.signature->isFoolConstantSymbol(true,functor)) {
        continue;
      }

      TermList resultType = env.signature->getFunction(functor)->fnType()->result();
      if (resultType == AtomicSort::boolSort()) {
        booleanTerm = subterm;
        goto substitution;
      }
    }
    literalPosition++;
  }

  // If we reached this point, it means that there was no boolean terms we are
  // interested in, so we don't infer anything
  return ClauseIterator::getEmpty();

  substitution:

  // Found a boolean term! Create the C[true] \/ s = false clause
  unsigned conclusionLength = premise->length() + 1;
  Clause* conclusion = new(conclusionLength) Clause(conclusionLength,
      GeneratingInference1(InferenceRule::FOOL_PARAMODULATION, premise));

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (unsigned i = 0; i < conclusion->length() - 1; i++) {
    (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*premise)[i], booleanTerm, troo) : (*premise)[i];
  }

  // Add s = false to the clause
  (*conclusion)[conclusion->length() - 1] = Literal::createEquality(true, booleanTerm, fols, AtomicSort::boolSort());

  return pvi(getSingletonIterator(conclusion));
}

}
