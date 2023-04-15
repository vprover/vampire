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

#if VHOL

#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/SortHelper.hpp"
#include "Shell/Statistics.hpp"
#include "BetaEtaISE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;


Clause* BetaEtaSimplify::simplify(Clause* c)
{
  CALL("BetaEtaSimplify::simplify");

  Literal* newLit;
  LiteralStack litStack;
  bool modified = false;

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    ASS(lit->isEquality());
    TermList t0 = *lit->nthArgument(0);
    TermList t1 = *lit->nthArgument(1);

    TermList t0r = t0.betaEtaNF();  
    TermList t1r = t1.betaEtaNF();       
    

    if((t0r != t0) || (t1r != t1)){
      modified = true;
      newLit = Literal::createEquality(lit->polarity(), t0r, t1r, SortHelper::getResultSort(t0.term()));
      litStack.push(newLit);
      continue;
    }      
    litStack.push(lit);  
  }

  if(!modified){
    return c;
  }

  Inference inf = SimplifyingInference1(InferenceRule::BETA_ETA_NORMALISE, c);
  Clause* newC = Clause::fromStack(litStack, inf);

  return newC;
}

#endif

