/**
 * @file FOOLParamodulation.cpp
 * Implements the inference rule, that is needed for efficient treatment of
 * term of the sort SRT_FOOL_BOOL. The details of why it is needed are in the
 * paper "A First Class Boolean Sort in First-Order Theorem Proving and TPTP"
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
#include "Kernel/Sorts.hpp"

#include "FOOLParamodulation.hpp"

namespace Inferences {

ClauseIterator FOOLParamodulation::generateClauses(Clause* premise) {
  CALL("FOOLParamodulation::generateClauses");

  /**
   * We are going to implement the following inference rule, taken from the paper:
   *
   *        C[s]
   * --------------------,
   * C[true] \/ s = false
   *
   * where s is a boolean term, that is not a variable, true or false,
   * C[s] is a clause with an occurrence of s, and C[true] is the C clause
   * with s substituted by true.
   */

  static TermList troo(Term::createConstant(Signature::FOOL_TRUE));
  static TermList fols(Term::createConstant(Signature::FOOL_FALSE));

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
    NonVariableIterator nvi(literals.next());
    while (nvi.hasNext()) {
      TermList subterm = nvi.next();
      unsigned functor = subterm.term()->functor();

      // we shouldn't replace boolean constants
      if (functor == Signature::FOOL_FALSE || functor == Signature::FOOL_TRUE) {
        continue;
      }

      unsigned resultType = env.signature->getFunction(functor)->fnType()->result();
      if (resultType == Sorts::SRT_FOOL_BOOL) {
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
  Inference* inference = new Inference1(Inference::FOOL_PARAMODULATION, premise);
  Clause* conclusion = new(conclusionLength) Clause(conclusionLength, premise->inputType(), inference);
  conclusion->setAge(premise->age() + 1);

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (unsigned i = 0; i < conclusion->length() - 1; i++) {
    (*conclusion)[i] = i == literalPosition ? EqHelper::replace((*premise)[i], booleanTerm, troo) : (*premise)[i];
  }

  // Add s = false to the clause
  (*conclusion)[conclusion->length() - 1] = Literal::createEquality(true, booleanTerm, fols, Sorts::SRT_FOOL_BOOL);

  return pvi(getSingletonIterator(conclusion));
}

}