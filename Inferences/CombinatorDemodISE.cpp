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
 * @file CombinatorDemodISE.cpp
 * Implements class CombinatorDemodISE.
 */

#include "Lib/Random.hpp"
#include "Lib/Environment.hpp"
#include "Lib/DArray.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SKIKBO.hpp"
#include "Kernel/SortHelper.hpp"
#include "Shell/Statistics.hpp"
#include "CombinatorDemodISE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

typedef ApplicativeHelper AH; 

Clause* CombinatorDemodISE::simplify(Clause* c)
{
  CALL("CombinatorDemodISE::simplify");

  Literal* newLit;
  LiteralStack litStack;
  bool modified = false;

 // cout << "into CombinatorDemodISE " + c->toString() << endl;

  unsigned length = 0;


  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    ASS(lit->isEquality());
    TermList t0 = *lit->nthArgument(0);
    TermList t1 = *lit->nthArgument(1);

    TermList t0r = headNormalForm(t0);  
    TermList t1r = headNormalForm(t1);     
    
    TermReducer tr;
    t0r = tr.transform(t0r);
    t1r = tr.transform(t1r);

    length = length + tr.getReductionLen();

    if((t0r != t0) || (t1r != t1)){
      modified = true;
      newLit = Literal::createEquality(lit->polarity(), TermList(t0r), TermList(t1r), SortHelper::getResultSort(t0.term()));
      litStack.push(newLit);
    } else {
      litStack.push(lit);
    }  
  }

  if(!modified){
    return c;
  }

  Inference inf = SimplifyingInference1(InferenceRule::COMBINATOR_DEMOD, c);
  inf.increaseReductions(length);
  Clause* newC = Clause::fromStack(litStack, inf);
  /*if(c->number() == 1620){
    cout << "out of CombinatorDemodISE " + newC->toString() << endl;
  }*/
  //if(!newC){ cout << "RETURNING NULL CLAUSE" << endl; }
  return newC;
}

TermList TermReducer::transformSubterm(TermList trm)
{
  CALL("TermReducer::transformSubterm");

  TermList res = CombinatorDemodISE::headNormalForm(trm);
  if(res != trm){
    _reducLen++;
  }
  return res;
}

TermList CombinatorDemodISE::headNormalForm(TermList t)
{
  CALL("CombinatorDemodISE::headNormalForm");

  static TermStack args;
  TermList head;
    
  for(;;){
    AH::getHeadAndArgs(t, head, args);
    if(AH::isComb(head) && !AH::isUnderApplied(head, args.size())){
      t = SKIKBO::reduce(args, head);
    } else {
      break; 
    }
  }
  return t;
}



