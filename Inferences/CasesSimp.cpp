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
 * @file CasesSimp.cpp
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
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "CasesSimp.hpp"

namespace Inferences {


ClauseIterator CasesSimp::performSimplification(Clause* premise, Literal* lit, TermList t) {
  CALL("CasesSimp::performSimplification");

  ASS(t.isTerm());

  static ClauseStack results;

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);

  if((t == lhs) || (t == rhs)){
    return ClauseIterator::getEmpty();
  }

  results.reset();

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  Literal* litFols = Literal::createEquality(true, t, fols, AtomicSort::boolSort());
  Literal* litTroo = Literal::createEquality(true, t, troo, AtomicSort::boolSort());


  unsigned conclusionLength = premise->length() + 1;
  Clause* conclusion1 = new(conclusionLength) Clause(conclusionLength, SimplifyingInference1(InferenceRule::CASES_SIMP, premise));
  Clause* conclusion2 = new(conclusionLength) Clause(conclusionLength, SimplifyingInference1(InferenceRule::CASES_SIMP, premise));

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (unsigned i = 0; i < conclusionLength - 1; i++) {
    Literal* curr = (*premise)[i];
    if(curr != lit){
      (*conclusion1)[i] = (*premise)[i];
      (*conclusion2)[i] = (*premise)[i];      
    } else {
      (*conclusion1)[i] = EqHelper::replace((*premise)[i], t, troo);
      (*conclusion2)[i] = EqHelper::replace((*premise)[i], t, fols);
    }
  }

  // Add s = false to the clause
  (*conclusion1)[conclusionLength - 1] = litFols;
  (*conclusion2)[conclusionLength - 1] = litTroo;

  results.push(conclusion1);
  results.push(conclusion2);

  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(results)));
}


struct CasesSimp::ResultFn
{
  ResultFn(Clause* cl, CasesSimp& parent) : _cl(cl), _parent(parent) {}
  ClauseIterator operator()(pair<Literal*, TermList> arg)
  {
    CALL("CasesSimp::ResultFn::operator()");
    
    return _parent.performSimplification(_cl, arg.first, arg.second);
  }
private:
  Clause* _cl;
  CasesSimp& _parent;
};

struct CasesSimp::RewriteableSubtermsFn
{
  RewriteableSubtermsFn() {}

  VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
  {
    CALL("CasesSimp::RewriteableSubtermsFn()");

    return pvi( pushPairIntoRightIterator(lit, 
                getUniquePersistentIterator(vi(new BooleanSubtermIt(lit)))));
  }

};


ClauseIterator CasesSimp::simplifyMany(Clause* premise)
{
  CALL("CasesSimp::generateClauses");

  auto it1 = premise->getLiteralIterator();
  auto it2 = getFilteredIterator(it1, isEqualityLit()); 

  auto it3 = getMapAndFlattenIterator(it2,RewriteableSubtermsFn());

  //Perform  Narrow
  auto it4 = getMapAndFlattenIterator(it3,ResultFn(premise, *this));

  return pvi( it4 );
}

}
