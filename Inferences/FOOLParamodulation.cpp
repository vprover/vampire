
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

#include "Saturation/SaturationAlgorithm.hpp"

#include "FOOLParamodulation.hpp"

namespace Inferences {

Clause* FOOLParamodulation::performParamodulation(Clause* premise, Literal* lit, TermList t) {
  CALL("FOOLParamodulation::performParamodulation");

  ASS(t.isTerm());

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);

  if((t == lhs) || (t == rhs)){
    return 0;
  }

  static TermList troo(Term::foolTrue());
  static TermList fols(Term::foolFalse());


  // Found a boolean term! Create the C[true] \/ s = false clause
  unsigned conclusionLength = premise->length() + 1;
  Inference* inference = new Inference1(Inference::FOOL_PARAMODULATION, premise);
  Clause* conclusion = new(conclusionLength) Clause(conclusionLength, premise->inputType(), inference);
  conclusion->setAge(premise->age() + 1);

  // Copy the literals from the premise except for the one at `literalPosition`,
  // that has the occurrence of `booleanTerm` replaced with false
  for (unsigned i = 0; i < conclusionLength - 1; i++) {
    Literal* curr = (*premise)[i];
    if(curr != lit){
      (*conclusion)[i] = (*premise)[i];
    } else {
      (*conclusion)[i] = EqHelper::replace((*premise)[i], t, troo);
    }
  }

  // Add s = false to the clause
  (*conclusion)[conclusionLength - 1] = Literal::createEquality(true, t, fols, Term::boolSort());

  return conclusion;
}


struct FOOLParamodulation::ResultFn
{
  ResultFn(Clause* cl, FOOLParamodulation& parent) : _cl(cl), _parent(parent) {}
  DECL_RETURN_TYPE(Clause*);
  OWN_RETURN_TYPE operator()(pair<Literal*, TermList> arg)
  {
    CALL("FOOLParamodulation::ResultFn::operator()");
    
    return _parent.performParamodulation(_cl, arg.first, arg.second);
  }
private:
  Clause* _cl;
  FOOLParamodulation& _parent;
};

struct FOOLParamodulation::RewriteableSubtermsFn
{
  RewriteableSubtermsFn(Ordering& ord) : _ord(ord) {}

  DECL_RETURN_TYPE(VirtualIterator<pair<Literal*, TermList> >);
  OWN_RETURN_TYPE operator()(Literal* lit)
  {
    CALL("FOOLParamodulation::RewriteableSubtermsFn()");

    return pvi( pushPairIntoRightIterator(lit, 
                EqHelper::getBooleanSubtermIterator(lit, _ord)) );
  }

private:
  Ordering& _ord;
};

ClauseIterator FOOLParamodulation::generateClauses(Clause* premise)
{
  CALL("FOOLParamodulation::generateClauses");

  auto it1 = premise->getSelectedLiteralIterator();

  auto it2 = getMapAndFlattenIterator(it1,RewriteableSubtermsFn(_salg->getOrdering()));

  //Perform  Narrow
  auto it3 = getMappingIterator(it2,ResultFn(premise, *this));

  auto it4 = getFilteredIterator(it3,NonzeroFn());

  return pvi( it4 );
}

}
