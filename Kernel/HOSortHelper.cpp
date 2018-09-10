
/*
 * File HOSortHelper.cpp.
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
 * @file HOSortHelper.cpp
 * Implements class HOSortHelper.
 */

#include "Lib/Environment.hpp"

#include "Clause.hpp"
#include "FormulaUnit.hpp"
#include "Signature.hpp"
#include "Sorts.hpp"
#include "SubformulaIterator.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "HOSortHelper.hpp"
#include "SortHelper.hpp"
#include "Shell/LambdaElimination.hpp"

using namespace Kernel;

/** 
 * Returns the sort of the head of an applicative term 
 * Cannot be called on a variable
 */
unsigned HOSortHelper::getHeadSort(TermList ts){
  CALL("HOSortHelper::getHeadSort");
  
  ASS(! ts.isVar());

  unsigned tsSort;
  Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
  while(sym->hOLAPP()){
    ts = *(ts.term()->nthArgument(0));
    tsSort = SortHelper::getArgSort(ts.term(), 0);
    if(ts.isVar()){ break; }
    sym = env.signature->getFunction(ts.term()->functor());
  }
  return tsSort;
}

//BAD CODE!
/** 
 * Returns the sort of the nth argument of the applicative term ts
 * argNum should be called prior to calling this function otherwise 
 * if n > argnum, an error will be thrown!
 */
unsigned HOSortHelper::getNthArgSort(TermList ts, unsigned n){
  CALL("HOSortHelper::getNthArgSort");

  unsigned argnum = argNum(ts);
  if(argnum <= n){ ASSERTION_VIOLATION; }
  for(unsigned i = argnum; i > n+1; i--){
    ts = *(ts.term()->nthArgument(0));    
  }
  ASS(ts.isTerm());
  //assuming getArgSort is 0 indexed
  return SortHelper::getArgSort(ts.term(), 1);  
}

/** 
 * Returns the number of args the head of an applicative term is applied to 
 */
unsigned HOSortHelper::argNum(TermList ts){
  CALL("HOSortHelper::argNum");
  
  unsigned arity = 0;
  
  if(ts.isVar()){
    return arity;
  } else {
    ASS(ts.isTerm());
    Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
    while(sym->hOLAPP()){
      arity++;
      ts = *(ts.term()->nthArgument(0));
      if(ts.isVar()){
        return arity;
      }
      sym = env.signature->getFunction(ts.term()->functor());
    }
    return arity;
  }  
  
}

/** 
 * Returns the resulting sort if a head of sort @b funcsort was to be applied to n arguments
 * If n is greater than arity of funcSort, the result sort is returned.
 */
unsigned HOSortHelper::appliedToN(unsigned funcSort, unsigned n){
  CALL("HOSortHelper::appliedToN");  
  
  ASS(n > 0);
  
  for(unsigned i = 0; i < n; i++){
    if(env.sorts->isOfStructuredSort(funcSort, Sorts::StructuredSort::HIGHER_ORD_CONST)){
      funcSort = range(funcSort);
    } else { 
      break;
    }
  }
  return funcSort;
}

/** 
 * 
 */
unsigned HOSortHelper::appliedToN(TermList ts, unsigned n){
  CALL("HOSortHelper::appliedToN");  
  
  ASS(ts.isTerm());
  
  unsigned termSort = SortHelper::getResultSort(ts.term()); 
  return appliedToN(termSort, n);
}


/** 
 * Returns the nth argument sort of functional sort @b funcSort
 */
unsigned HOSortHelper::getNthArgSort(unsigned funcSort, unsigned n){
  CALL("HOSortHelper::getNthArgSort");  

  ASS(n >= 0);
  
  for(unsigned i = 0; i < n; i++){
    funcSort = range(funcSort);
  }
  return domain(funcSort);
}

/**
 * Returns the head symbol of an applicative term 
 */
//shouldn't really be here as not a sort function
TermList HOSortHelper::getHead(TermList ts){
  CALL("HOSortHelper::getHead");  
  
  if(ts.isVar()){
    return ts;
  } else {
    ASS(ts.isTerm());
    Signature::Symbol* sym = env.signature->getFunction(ts.term()->functor());
    while(sym->hOLAPP()){
      ts = *(ts.term()->nthArgument(0));
      if(ts.isVar()){
        return ts;
      }
      sym = env.signature->getFunction(ts.term()->functor());
    }
    return ts;
  }
  
}

/**
 *  Converts a HOTerm struct into applicative form TermList
 */
TermList HOSortHelper::HOTerm::appify(){
  CALL("HOSortHelper::HOTerm::appify");   
  
  TermList ts = head;
  unsigned sort = headsort;
  while(!args.isEmpty()){
    unsigned fun = LambdaElimination::introduceAppSymbol(sort, sorts.pop_front(), range(sort));
    sort = range(sort);
    LambdaElimination::buildFuncApp(fun, ts, args.pop_front(), ts);
  }
  ASS(sorts.isEmpty());
  return ts;
}

unsigned HOSortHelper::arity(unsigned sort){
  CALL("HOSortHelper::arity"); 
  
  if(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST))
  {
    return env.sorts->getFuncSort(sort)->arity();
  }
  return 0;
}

/** Given a functional sort, returns its range */
unsigned HOSortHelper::range(unsigned sort){
  CALL("HOSortHelper::range"); 
  
  ASS(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST));
  
  unsigned range = env.sorts->getFuncSort(sort)->getRangeSort();
  return range;  
}

/** Given a functional sort, returns its domain */
unsigned HOSortHelper::domain(unsigned sort){
  CALL("HOSortHelper::domain");  

  ASS(env.sorts->isOfStructuredSort(sort, Sorts::StructuredSort::HIGHER_ORD_CONST));
  
  unsigned dom = env.sorts->getFuncSort(sort)->getDomainSort();
  return dom;
}
