
/*
 * File HOTerm.cpp.
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
 * @file HOTerm.cpp
 * Implements class HOTerm.
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
  * Prints out HOTerm
  */
#if VDEBUG
vstring HOTerm::HOTerm::toString(bool withSorts, bool withIndices) const
{
  CALL("HOTerm::HOTerm::toString");   
  
  vstring res;
  if(!withSorts){
    vstring tween = (withIndices && _head.isVar()) ? "/" + Int::toString(_headInd) : "";
    res = _head.toString() + tween +  " ";
  } else {
    res = _head.toString() + "_" + env.sorts->sortName(_headsort) + " ";
  }
  for(unsigned i = 0; i < argnum(); i++){
    HOTerm* ht = _args[i]
    if(!ht->argnum()){
      res = res + ht->toString(withSorts, withIndices);
    } else {
      res = res + "(" + ht->toString(withSorts, withIndices) + ")";
    }
  }
  return res;
}
#endif

void HOTerm::HOTerm::headify(HOTerm* tm){
  CALL("HOTerm::HOTerm::headify");   
 
  _head = tm->head;
  headsort = tm->headsort;
  headInd = tm.headInd;
  while(!tm.args.isEmpty()){
    args.push_front(tm.args.pop_back());
  }  
}


/** view comment in .hpp file */
bool HOTerm::HOTerm::equal(const HOTerm& ht,bool useIndices) const
{
  CALL("HOTerm::HOTerm::equal");
  
  Stack<HOTerm> toDo;
  toDo.push(*this);
  toDo.push(ht);
  
  while(!toDo.isEmpty()){
    HOTerm ht1 = toDo.pop();
    HOTerm ht2 = toDo.pop();
    if(ht1.varHead() && ht2.varHead()){
      if(useIndices){
        if(ht1.headInd != ht2.headInd){
          return false;
        }
      } 
      if(ht1.head.var() != ht2.head.var()){
        return false;
      }
    } else if(ht1.head.isTerm() && ht2.head.isTerm()){
      if(ht1.head.term()->functor() != ht2.head.term()->functor()){
        return false;
      }
    } else {
      return false;
    }
    if(ht1.argnum() != ht2.argnum()){ return false; }
    for(unsigned i = 0; i < ht1.argnum(); i++){
      toDo.push(ht1.ntharg(i));
      toDo.push(ht2.ntharg(i));
    }
  }

  return true;
}