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
 * @file PrimitiveInstantiation.cpp
 * Implements class PrimitiveInstantiation.
 */

#include "Debug/RuntimeStatistics.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/ApplicativeHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/DHSet.hpp"

#include "ElimLeibniz.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

namespace Inferences
{
  
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


typedef ApplicativeHelper AH;

bool ElimLeibniz::polarity(Literal* lit) {
  CALL("ElimLeibniz::polarity");

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);
  ASS(AH::isBool(lhs)  || AH::isBool(rhs));
  if(AH::isBool(lhs)){ 
    return lit->polarity() == AH::isTrue(lhs);
  }
  return lit->polarity() == AH::isTrue(rhs);
}

bool ElimLeibniz::isPair(Literal* l1, Literal* l2){
  CALL("ElimLeibniz::isPair");
  ASS(polarity(l1)  != polarity(l2));

  LeibEqRec ler1 = getLiteralInfo(l1);
  LeibEqRec ler2 = getLiteralInfo(l2);
  return ler1.var == ler2.var;
}

ElimLeibniz::LeibEqRec ElimLeibniz::getLiteralInfo(Literal* lit){
  CALL("ElimLeibniz::getLiteralInfo");

  TermList lhs = *lit->nthArgument(0);
  TermList rhs = *lit->nthArgument(1);
  TermList nonBooleanSide = AH::isBool(rhs) ? lhs : rhs;
  ASS(nonBooleanSide.isTerm());
  Term* term = nonBooleanSide.term();

  LeibEqRec ler;
  ler.var = term->nthArgument(2)->var();
  ler.arg = *term->nthArgument(3);
  ler.argSort = *term->nthArgument(0);

  return ler;
}

Clause* ElimLeibniz::createConclusion(Clause* premise, Literal* newLit, 
                                      Literal* posLit, Literal* negLit, RobSubstitution& subst){
  CALL("ElimLeibniz::createConclusion");

  unsigned newLen=premise->length() - 1;
  Clause* res = new(newLen) Clause(newLen, GeneratingInference1(InferenceRule::LEIBNIZ_ELIMINATION, premise));
  Literal* newLitAfter = subst.apply(newLit, 0);

  unsigned next = 0;
  for(unsigned i=0;i<premise->length();i++) {
    Literal* curr=(*premise)[i];
    if(curr!=posLit && curr!=negLit){
      Literal* currAfter = subst.apply(curr, 0);
      (*res)[next++] = currAfter;
    }
  }
  (*res)[next++] = newLitAfter;
  ASS_EQ(next,newLen);
  return res;
}

ClauseIterator ElimLeibniz::generateClauses(Clause* premise)
{
  CALL("ElimLeibniz::generateClauses");

  typedef SortHelper SH;

  static TermStack args;
  TermList head;

  Stack<Literal*> positiveLits;
  Stack<Literal*> negativeLits;

  Literal* posLit;
  Literal* negLit;

  for(unsigned i = 0; i < premise->length(); i++){
    Literal* lit = (*premise)[i];
    TermList lhs = *lit->nthArgument(0);
    TermList rhs = *lit->nthArgument(1);
    if(!AH::isBool(lhs) && !AH::isBool(rhs)){ continue; } 
    TermList nonBooleanSide = AH::isBool(rhs) ? lhs : rhs;

    AH::getHeadAndArgs(nonBooleanSide, head, args);
    if(!head.isVar() || args.size() != 1){ continue; }
    
    bool pol = polarity(lit);
    unsigned size = pol ? negativeLits.size() : positiveLits.size();

    for(unsigned j = 0; j <size; j++){
      Literal* lit2 = pol ? negativeLits[j] : positiveLits[j];
      if(isPair(lit, lit2)){
        posLit = pol ? lit : lit2;
        negLit = pol ? lit2 : lit;
        goto afterLoop;
      } 
    }
    if(pol){ positiveLits.push(lit); } else 
           { negativeLits.push(lit); }
  }
  
  return ClauseIterator::getEmpty();  

afterLoop:

  ClauseStack clauses;
  static RobSubstitution subst;
  subst.reset();
 
  LeibEqRec lerPosLit = getLiteralInfo(posLit);
  LeibEqRec lerNegLit = getLiteralInfo(negLit);
  TermList argS = lerNegLit.argSort;

  Literal* newLit = Literal::createEquality(true, lerPosLit.arg, lerNegLit.arg, argS);

  TermList var = TermList(lerPosLit.var, false);

  TermList vEquals = TermList(Term::create1(env.signature->getEqualityProxy(), argS));
  TermList t1 = AH::createAppTerm(SH::getResultSort(vEquals.term()), vEquals, lerNegLit.arg);
  if(subst.unify(var, 0, t1, 0)){
    Clause* c = createConclusion(premise, newLit, posLit, negLit, subst);
    clauses.push(c);
    subst.reset();
  }

  TermList t2 = AH::createAppTerm(SH::getResultSort(vEquals.term()), vEquals, lerPosLit.arg);
  
  TermList typeArgs[] = {argS, AtomicSort::boolSort(), AtomicSort::boolSort()};
  unsigned b_comb = env.signature->getCombinator(Signature::B_COMB);
  
  TermList bComb  = TermList(Term::create(b_comb, 3, typeArgs));
  TermList vNot   = TermList(Term::createConstant(env.signature->getNotProxy()));
  t2 = AH::createAppTerm3(SH::getResultSort(bComb.term()), bComb,vNot,t2);

  if(subst.unify(var, 0, t2, 0)){
    Clause* c = createConclusion(premise, newLit, posLit, negLit, subst);
    clauses.push(c);
  }  

  env.statistics->leibnizElims++;
  return pvi(getUniquePersistentIterator(ClauseStack::Iterator(clauses)));

}

}
