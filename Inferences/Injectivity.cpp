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
  TermList lhsS = *(sideLit->nthArgument(0));
  TermList rhsS = *(sideLit->nthArgument(1));

  static TermStack argsLhs;//No need to reset because getHeadAndArgs resets
  static TermStack argsRhs;
  TermStack termArgs;
  TermList argLhs, argRhs, headLhs, headRhs, differingArg;

  ApplicativeHelper::getHeadAndArgs(lhsM, headLhs, argsLhs);
  ApplicativeHelper::getHeadAndArgs(rhsM, headRhs, argsRhs);
  if(headLhs != headRhs || headLhs.isVar() || 
    ApplicativeHelper::isComb(headLhs)){
    return ClauseIterator::getEmpty();
  }
  ASS(argsLhs.size() == argsRhs.size());

  bool differingArgFound = false;
  unsigned index = 0;
  termArgs.push(lhsM);
  while(!argsLhs.isEmpty()){
    argLhs = argsLhs.pop();
    argRhs = argsRhs.pop();
    if(!argLhs.isVar() || !argRhs.isVar()){
      return ClauseIterator::getEmpty();
    }
    if(argLhs != argRhs){
      if(differingArgFound){
        return ClauseIterator::getEmpty();
      }
      if((argLhs == lhsS && argRhs == rhsS) ||
         (argLhs == rhsS && argRhs == lhsS)){
        differingArg = argLhs;
        differingArgFound = true;
      } else {
        return ClauseIterator::getEmpty();        
      }
    } else {
      termArgs.push(argLhs);
    }
    if(!differingArgFound){ index++; }
  }

  //at this point, we know the clause is of the form f x1 y x2... = f x1 z x2 ... \/ x != y 
  //index holds the index of the different argument
  TermList newLhs = createNewLhs(headLhs, termArgs, index);
  TermList sort = SortHelper::getResultSort(newLhs.term());
  Literal* lit = Literal::createEquality(true, newLhs, differingArg, sort);

  Clause* conclusion = new(1) Clause(1, GeneratingInference1(InferenceRule::INJECTIVITY, premise));

  (*conclusion)[0] = lit;

  return pvi(getSingletonIterator(conclusion));
}

TermList Injectivity::createNewLhs(TermList oldhead, TermStack& termArgs, unsigned index){
  CALL("Injectivity::createNewLhs");

  TermList* typeArg = oldhead.term()->args();
  TermStack typeArgs;
  while(!typeArg->isEmpty()){
    typeArgs.push(*typeArg);
    typeArg = typeArg->next();
  }

  Signature::Symbol* func = env.signature->getFunction(oldhead.term()->functor());
  vstring pref = "inv_" + func->name() + "_";
  unsigned iFunc = env.signature->addFreshFunction(func->arity(), pref.c_str() ); 

  OperatorType* funcType = func->fnType();
  TermList type = funcType->result(); 

  TermList oldResult = ApplicativeHelper::getResultApplieadToNArgs(type, termArgs.size());
  TermStack sorts;
  TermList newResult;

  sorts.push(oldResult); 
  for(unsigned i = 1; i <= termArgs.size(); i++){
    if(i - 1 != index){
      sorts.push(ApplicativeHelper::getNthArg(type,i));
    } else {
      newResult = ApplicativeHelper::getNthArg(type,i);
    }
  }

  TermList inverseType = AtomicSort::arrowSort(sorts, newResult);

  OperatorType* invFuncType = OperatorType::getConstantsType(inverseType, funcType->typeArgsArity());
  Signature::Symbol* invFunc = env.signature->getFunction(iFunc);
  invFunc->setType(invFuncType);
  TermList invFuncHead = TermList(Term::create(iFunc, func->arity(), typeArgs.begin()));

  TermList invFuncHeadType = SortHelper::getResultSort(invFuncHead.term());
  return ApplicativeHelper::createAppTerm(invFuncHeadType, invFuncHead, termArgs);  
}


}
