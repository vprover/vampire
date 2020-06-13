
/*
 * File FOOLParamodulation.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
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
#include "Kernel/Sorts.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "CasesSimp.hpp"

namespace Inferences {

ClauseIterator CasesSimp::simplifyMany(Clause* premise) {
  CALL("CasesSimp::generateClauses");

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());
  static ClauseStack results;
  results.reset();

  TermList booleanTerm;
  unsigned literalPosition = 0;

  for(unsigned i = 0; i < premise->length(); i++){
    Literal* literal = (*premise)[i];
   
    ASS(literal->isEquality())
    TermList lhs = *literal->nthArgument(0);
    TermList rhs = *literal->nthArgument(1);

    NonVariableNonTypeIterator nvi(literal);
    while (nvi.hasNext()) {
      TermList subterm = nvi.next();

      // we shouldn't replace boolean constants
      if (ApplicativeHelper::isBool(subterm) ||
          (subterm == lhs) || (subterm ==rhs)) {
        continue;
      }

      TermList resultType =  SortHelper::getResultSort(subterm.term());
      if (resultType == Term::boolSort()) {
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

  Literal* litFols = Literal::createEquality(true, booleanTerm, fols, Term::boolSort());
  Literal* litTroo = Literal::createEquality(true, booleanTerm, troo, Term::boolSort());

  unsigned conclusionLength = premise->length() + 1;
  Inference* inference1 = new Inference1(Inference::CASES_SIMP, premise);
  Inference* inference2 = new Inference1(Inference::CASES_SIMP, premise);
  Clause* conclusion1 = new(conclusionLength) Clause(conclusionLength, premise->inputType(), inference1);
  Clause* conclusion2 = new(conclusionLength) Clause(conclusionLength, premise->inputType(), inference2);
  conclusion1->setAge(premise->age());
  conclusion2->setAge(premise->age());

  for (unsigned i = 0; i < conclusionLength - 1; i++) {
    if(i == literalPosition){
      (*conclusion1)[i] = EqHelper::replace((*premise)[i], booleanTerm, troo);
      (*conclusion2)[i] = EqHelper::replace((*premise)[i], booleanTerm, fols);
    } else {
      (*conclusion1)[i] = (*premise)[i];
      (*conclusion2)[i] = (*premise)[i];      
    }
  }

  (*conclusion1)[conclusionLength - 1] = litFols;
  (*conclusion2)[conclusionLength - 1] = litTroo;

  results.push(conclusion1);
  results.push(conclusion2);

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
}

}
