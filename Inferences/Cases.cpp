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
#include "Kernel/SortHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Cases.hpp"

namespace Inferences {

using namespace std;

Clause* Cases::performParamodulation(Clause* premise, Literal* lit, TermList t) {
  ASS(t.isTerm());

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);

  if((t == lhs) || (t == rhs)){
    return 0;
  }

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());


  // Found a boolean term! Create the C[true] \/ s = false clause

  RStack<Literal*> resLits;

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (Literal* curr : iterTraits(premise->iterLits())) {
    resLits->push( curr != lit 
        ? curr
        : EqHelper::replace(curr, t, troo));
  }

  // Add s = false to the clause
  resLits->push(Literal::createEquality(true, t, fols, AtomicSort::boolSort()));

  return Clause::fromStack(*resLits, GeneratingInference1(InferenceRule::FOOL_PARAMODULATION, premise));
}


struct Cases::ResultFn
{
  ResultFn(Clause* cl, Cases& parent) : _cl(cl), _parent(parent) {}
  Clause* operator()(pair<Literal*, TermList> arg)
  {
    return _parent.performParamodulation(_cl, arg.first, arg.second);
  }
private:
  Clause* _cl;
  Cases& _parent;
};

struct Cases::RewriteableSubtermsFn
{
  RewriteableSubtermsFn(Ordering& ord) : _ord(ord) {}

  VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
  {
    return pvi( pushPairIntoRightIterator(lit, 
                EqHelper::getBooleanSubtermIterator(lit, _ord)) );
  }

private:
  Ordering& _ord;
};

ClauseIterator Cases::generateClauses(Clause* premise)
{
  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getMapAndFlattenIterator(it1,RewriteableSubtermsFn(_salg->getOrdering()));

  auto it3 = getMappingIterator(it2,ResultFn(premise, *this));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  return pvi( it4 );
}

}
