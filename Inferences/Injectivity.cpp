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
 * @file Injectivity.cpp
 * Every Injective function has a left-inverse
 * creates a Skolem to act as left-inverse funcion
 */

#if VHOL

#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"

#include "Injectivity.hpp"

namespace Inferences {

ClauseIterator Injectivity::generateClauses(Clause* premise) {
  CALL("Injectivity::generateClauses");

  if(premise->length() != 2){
    return ClauseIterator::getEmpty();
  }

  Literal* mainLit;
  Literal* sideLit;
  Literal* lit0 = (*premise)[0];
  Literal* lit1 = (*premise)[1];
  if(!lit0->isTwoVarEquality() && lit1->isTwoVarEquality() && 
     !lit0->polarity() && lit1->polarity()){
    mainLit = lit0;
    sideLit = lit1;
  }else if(!lit1->isTwoVarEquality() && lit0->isTwoVarEquality() &&
           !lit1->polarity() && lit0->polarity()) {
    mainLit = lit1;
    sideLit = lit0;
  }else{
    return ClauseIterator::getEmpty();
  }

  TermList lhsM = *(mainLit->nthArgument(0));
  TermList rhsM = *(mainLit->nthArgument(1));
  if(lhsM.isLambdaTerm() || rhsM.isLambdaTerm())
  { return ClauseIterator::getEmpty(); }

  TermList lhsS = *(sideLit->nthArgument(0));
  TermList rhsS = *(sideLit->nthArgument(1));

  static TermStack argsLhs;//No need to reset because getHeadAndArgs resets
  static TermStack argsRhs;  
  TermStack termArgs;

  TermStack argSorts; // sorts of argsLhs and argsRhs (not instantiated!)
  TermStack termArgSorts;
  TermList headLhs, headRhs, differingArg, differingArgSort;

  ApplicativeHelper::getHeadAndArgs(lhsM, headLhs, argsLhs);
  ApplicativeHelper::getHeadAndArgs(rhsM, headRhs, argsRhs);

  if(headLhs != headRhs || headLhs.isVar())
  { return ClauseIterator::getEmpty(); }
  // assertion below holds, since lhsM and rhsM have same types and neither is a lambda term
  ASS(argsLhs.size() == argsRhs.size());


  // TODO inelegant stuff here
  // THe reason we get the sorts from the type instead of using getHeadArgsAndSorts
  // is become we want the original non-instantiated sorts...
  TermList headLhsSort = env.signature->getFunction(headLhs.term()->functor())->fnType()->result();
  for(unsigned i = 0; i < argsLhs.size(); i++){
    argSorts.push(headLhsSort.domain());
    headLhsSort = headLhsSort.result();
  }

  bool differingArgFound = false;
  termArgs.push(lhsM);
  termArgSorts.push(headLhsSort);
  int idx = argSorts.size() - 1;
  while(!argsLhs.isEmpty()){
    TermList argLhs = argsLhs.pop();
    TermList argRhs = argsRhs.pop();
    TermList sort   = argSorts[idx];
    if(!argLhs.isVar() || !argRhs.isVar()){
      return ClauseIterator::getEmpty();
    }
    if(argLhs != argRhs){
      if(differingArgFound){
        return ClauseIterator::getEmpty();
      }
      if((argLhs == lhsS && argRhs == rhsS) ||
         (argLhs == rhsS && argRhs == lhsS)){
        differingArg      = argLhs;
        differingArgSort  = sort;
        differingArgFound = true;
      } else {
        return ClauseIterator::getEmpty();        
      }
    } else {
      termArgs.push(argLhs);
      termArgSorts.push(sort);
    }
    idx--;
  }

  env.statistics->injectiveFunInverses++;

  //at this point, we know the clause is of the form f x1 y x2... != f x1 z x2 ... \/ x = y 
  TermList newLhs = createNewLhs(headLhs, termArgs, AtomicSort::arrowSort(termArgSorts, differingArgSort));
  Literal* lit = Literal::createEquality(true, newLhs, differingArg, differingArgSort);

  Clause* conclusion = new(1) Clause(1, GeneratingInference1(InferenceRule::INJECTIVITY, premise));

  (*conclusion)[0] = lit;

  return pvi(getSingletonIterator(conclusion));
}

TermList Injectivity::createNewLhs(TermList oldhead, TermStack& termArgs, TermList invFunSort){
  CALL("Injectivity::createNewLhs");

  TermList* typeArg = oldhead.term()->args();
  TermStack typeArgs;
  while(!typeArg->isEmpty()){
    typeArgs.push(*typeArg);
    typeArg = typeArg->next();
  }

  Signature::Symbol* func = env.signature->getFunction(oldhead.term()->functor());
  vstring pref = "inv_" + func->name() + "_";
  unsigned iFunc = env.signature->addFreshFunction(oldhead.term()->arity(), pref.c_str() ); 

  OperatorType* invFuncType = OperatorType::getConstantsType(invFunSort, oldhead.term()->arity());
  Signature::Symbol* invFunc = env.signature->getFunction(iFunc);

  invFunc->setType(invFuncType);
  TermList invFuncHead = TermList(Term::create(iFunc, func->arity(), typeArgs.begin()));

  return ApplicativeHelper::app(invFuncHead, termArgs);  
}


}

#endif