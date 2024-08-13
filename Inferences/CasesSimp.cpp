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

using namespace std;
using namespace Lib;

ClauseIterator CasesSimp::performSimplification(Clause* premise, Literal* lit, TermList t) {
  ASS(t.isTerm());

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);

  if((t == lhs) || (t == rhs)){
    return ClauseIterator::getEmpty();
  }

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());

  Literal* litFols = Literal::createEquality(true, t, fols, AtomicSort::boolSort());
  Literal* litTroo = Literal::createEquality(true, t, troo, AtomicSort::boolSort());


  RStack<Literal*> resLits1;
  RStack<Literal*> resLits2;

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (auto curr : premise->iterLits()) {
    resLits1->push(curr != lit ? curr : EqHelper::replace(curr, t, troo));
    resLits2->push(curr != lit ? curr : EqHelper::replace(curr, t, fols));
  }

  // Add s = false to the clause
  resLits1->push(litFols);
  resLits2->push(litTroo);

  return pvi(iterItems(
    Clause::fromStack(*resLits1, SimplifyingInference1(InferenceRule::CASES_SIMP, premise)),
    Clause::fromStack(*resLits2, SimplifyingInference1(InferenceRule::CASES_SIMP, premise))
  ));
}


struct CasesSimp::ResultFn
{
  ResultFn(Clause* cl, CasesSimp& parent) : _cl(cl), _parent(parent) {}
  ClauseIterator operator()(pair<Literal*, TermList> arg)
  {
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
    return pvi( pushPairIntoRightIterator(lit, 
                getUniquePersistentIterator(vi(new BooleanSubtermIt(lit)))));
  }

};


ClauseIterator CasesSimp::simplifyMany(Clause* premise)
{
  auto it1 = premise->getLiteralIterator();
  auto it2 = getFilteredIterator(it1, isEqualityLit()); 

  auto it3 = getMapAndFlattenIterator(it2,RewriteableSubtermsFn());

  //Perform  Narrow
  auto it4 = getMapAndFlattenIterator(it3,ResultFn(premise, *this));

  return pvi( it4 );
}

}
