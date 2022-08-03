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
 * @file CombinatorNormalisationISE.cpp
 * Implements class CombinatorNormalisationISE.
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
#include "Kernel/Signature.hpp"
#include "Shell/Statistics.hpp"
#include "CombinatorNormalisationISE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;

typedef ApplicativeHelper AH; 

Clause* CombinatorNormalisationISE::simplify(Clause* c)
{
  CALL("CombinatorNormalisationISE::simplify");

  Literal* newLit;
  LiteralStack litStack;
  bool modified = false;

 // cout << "into CombinatorNormalisationISE " + c->toString() << endl;

  for(unsigned i = 0; i < c->length(); i++){
    Literal* lit = (*c)[i];
    ASS(lit->isEquality());
    TermList t0 = *lit->nthArgument(0);
    TermList t1 = *lit->nthArgument(1);
  
    // TermTransformer does not transform at the top level hence call below
    TermList t0r = replaceWithSmallerCombinator(t0);
    TermList t1r = replaceWithSmallerCombinator(t1);

    CombinatorNormaliser cn;
    t0r = cn.transform(t0r);
    t1r = cn.transform(t1r);
    
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

  Clause* newC = Clause::fromStack(litStack, SimplifyingInference1(InferenceRule::COMBINATOR_NORMALISE, c));
  
  return newC;
}

TermList CombinatorNormaliser::transformSubterm(TermList trm)
{
  CALL("CombinatorSimplifier::transformSubterm");

  return CombinatorNormalisationISE::replaceWithSmallerCombinator(trm);
}

TermList CombinatorNormalisationISE::replaceWithSmallerCombinator(TermList t)
{
  CALL("CombinatorNormalisationISE::replaceWithSmallerCombinator");

  static TermStack args;
  static TermStack args1;
  static TermStack args2;
  TermList head;
  TermList head1;
  TermList head2;
  
  TermList sort;
  if(t.isTerm()){
    sort = SortHelper::getResultSort(t.term());
  }

  //cout << "The original term is " + t.toString() << endl;

  AH::getHeadAndArgs(t, head, args);
  if(AH::isComb(head) && (args.size() == 1 || args.size() == 2)){
    Signature::Combinator comb = AH::getComb(head);
    switch(comb){
      case Signature::S_COMB: {
        if(args.size() == 1){
          TermList arg1 = args[0];
          AH::getHeadAndArgs(arg1, head1, args1);
          if(args1.size() == 1 && 
             AH::isComb(head1) && (AH::getComb(head1) == Signature::C_COMB  || 
                                   AH::getComb(head1) == Signature::S_COMB) &&
             AH::isComb(args1[0]) && AH::getComb(args1[0]) == Signature::K_COMB){
            //S (C K) = I /\ S (S K) = I
            return TermList(Term::create1(env.signature->getCombinator(Signature::I_COMB), AH::getNthArg(sort,1)));
          }
          if(args1.size() == 2 &&
             AH::isComb(head1) && AH::getComb(head1) == Signature::B_COMB &&
             AH::isComb(args1[1]) && AH::getComb(args1[1]) == Signature::K_COMB){
            TermList s1 = AH::getNthArg(SortHelper::getResultSort(head1.term()), 2);
            TermList s2 = AH::getNthArg(sort, 1);
            return createKTerm(s1, s2, args1[0]);
          }
        }
        if(args.size() == 2){
          TermList arg1 = args[1];
          TermList arg2 = args[0];
          if(AH::isComb(arg1) && AH::getComb(arg1) == Signature::K_COMB){
            return TermList(Term::create1(env.signature->getCombinator(Signature::I_COMB), AH::getNthArg(sort,1)));
          }
          AH::getHeadAndArgs(arg1, head1, args1);
          if(args1.size() == 2 &&
             AH::isComb(head1) && AH::getComb(head1) == Signature::B_COMB &&
             AH::isComb(args1[1]) && AH::getComb(args1[1]) == Signature::K_COMB){
            return args1[0];
          }                    
          AH::getHeadAndArgs(arg2, head2, args2);
          bool arg2isKY = args2.size() == 1 && AH::isComb(head2) && AH::getComb(head2) == Signature::K_COMB; 
          bool arg1isKX = args1.size() == 1 && AH::isComb(head1) && AH::getComb(head1) == Signature::K_COMB;
          if(arg1isKX){
            if(arg2isKY){
              TermList xSort = AH::getNthArg(SortHelper::getResultSort(head1.term()), 1);
              TermList xy = AH::createAppTerm(xSort, args1[0], args2[0]);
              TermList s1 = SortHelper::getResultSort(xy.term());
              TermList s2 = AH::getNthArg(sort, 1);
              return createKTerm(s1, s2, xy);
            }
            if(!args2.size() && AH::isComb(head2) && AH::getComb(head2) == Signature::I_COMB){
              return args1[0];
            }
            TermList arg1sort = AH::getNthArg(SortHelper::getResultSort(head1.term()),1);
            TermList arg2sort = AH::getNthArg(SortHelper::getResultSort(head.term()),2);
            return createSCorBTerm(args1[0], arg1sort, args[0], arg2sort, Signature::B_COMB);
          }
          if(arg2isKY){
            TermList arg1sort = AH::getNthArg(SortHelper::getResultSort(head.term()),1);
            TermList arg2sort = AH::getNthArg(SortHelper::getResultSort(head2.term()),1);
            return createSCorBTerm(args[1], arg1sort, args2[0], arg2sort, Signature::C_COMB);    
          }
        }
      }
      break;
      case Signature::B_COMB : {
        if(args.size() == 1){
          if(AH::isComb(args[0]) && AH::getComb(args[0]) == Signature::I_COMB){
            return TermList(Term::create1(env.signature->getCombinator(Signature::I_COMB), AH::getNthArg(sort,1)));
          }
        }
        if(args.size() == 2){
          if(AH::isComb(args[0]) && AH::getComb(args[0]) == Signature::I_COMB){
            return args[1];
          }          
          AH::getHeadAndArgs(args[0], head2, args2);
          bool arg2isKY = args2.size() == 1 && AH::isComb(head2) && AH::getComb(head2) == Signature::K_COMB; 
          if(arg2isKY){
            TermList xSort = AH::getNthArg(SortHelper::getResultSort(head.term()), 1);
            TermList xy = AH::createAppTerm(xSort, args[1], args2[0]);
            TermList s1 = SortHelper::getResultSort(xy.term());
            TermList s2 = AH::getNthArg(sort, 1);
            return createKTerm(s1, s2, xy);  
          }
        }
      }
      break;
      case Signature::C_COMB : {
        if(args.size() == 1){
          TermList arg1 = args[0];
          AH::getHeadAndArgs(arg1, head1, args1);
          if(args1.size() == 1 &&
             AH::isComb(head1) && AH::getComb(head1) == Signature::C_COMB){
            return args1[0]; //C (C t) = t
          }          
        }
        if(args.size() == 2){
          AH::getHeadAndArgs(args[1], head1, args1);
          bool arg1isKX = args1.size() == 1 && AH::isComb(head1) && AH::getComb(head1) == Signature::K_COMB;
          if(arg1isKX){
            TermList xSort = AH::getNthArg(SortHelper::getResultSort(head1.term()), 1);
            TermList xy = AH::createAppTerm(xSort, args1[0], args[0]);
            TermList s1 = SortHelper::getResultSort(xy.term());
            TermList s2 = AH::getNthArg(sort, 1);
            return createKTerm(s1, s2, xy);   
          } 
        }
      }
      break;
      default: {}

    }
  }

  return t;
}

TermList CombinatorNormalisationISE::createKTerm(TermList s1, TermList s2, TermList arg1)
{
  CALL("CombinatorNormalisationISE::createKTerm");
  
  unsigned kcomb = env.signature->getCombinator(Signature::K_COMB);
  TermList res = TermList(Term::create2(kcomb, s1, s2));
  res = AH::createAppTerm(SortHelper::getResultSort(res.term()), res, arg1);             
  return res;
}   
    
TermList CombinatorNormalisationISE::createSCorBTerm(TermList arg1, TermList arg1sort,
          TermList arg2, TermList arg2sort, Signature::Combinator comb)
{
  CALL("CombinatorNormalisationISE::createSCorBTerm");
  
  TermList s1, s2, s3;
  unsigned cb = env.signature->getCombinator(comb);
  
  if(comb == Signature::S_COMB || comb == Signature::C_COMB){
    //cout << "CCOMB arg1 " + arg1.toString() + " of sort " + arg1sort.toString() << endl; 
    s1 = AH::getNthArg(arg1sort, 1);
    s2 = AH::getNthArg(arg1sort, 2);
    s3 = AH::getResultApplieadToNArgs(arg1sort, 2);
  } else {
    //cout << "BCOMB arg1 " + arg1.toString() + " of sort " + arg1sort.toString() << endl; 
    s1 = AH::getNthArg(arg2sort, 1);
    s2 = AH::getNthArg(arg1sort, 1);
    s3 = AH::getResultApplieadToNArgs(arg1sort, 1);
  }
  
  TermList args[] = {s1, s2, s3};
  TermList c = TermList(Term::create(cb, 3, args));
  return AH::createAppTerm3(SortHelper::getResultSort(c.term()), c, arg1, arg2); 
}



