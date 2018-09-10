
/*
 * File CombUnification.cpp.
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
 * @file CombUnification.cpp
 * Implements polynomial modification of the Robinson unification algorithm.
 */

#include "Lib/Environment.hpp"

#include "Lib/Hash.hpp"
#include "Lib/DArray.hpp"
#include "Lib/List.hpp"
#include "Lib/Random.hpp"
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/SkipList.hpp"
#include "Lib/Int.hpp"

#include "Clause.hpp"
#include "Renaming.hpp"
#include "SortHelper.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Signature.hpp"
#include "HOSortHelper.hpp"

#include "Indexing/TermSharing.hpp"

#include "CombUnification.hpp"

#if VDEBUG
#include "Lib/Int.hpp"
#include "Debug/Tracer.hpp"
#include <iostream>
using namespace Debug;
#endif

namespace Kernel
{

using namespace std;
using namespace Lib;

void CombSubstitution::populateTransformations()
{
  CALL("CombSubstitution::populateTransformations");

  UnificationPair up = _unificationPairs.top();
  TTPair topPair = up.unifPair;
  TermSpec tsLeft = topPair.first;
  TermSpec tsRght = topPair.second; 

  HOSortHelper::HOTerm hoterml = HOSortHelper::HOTerm(tsLeft.term);
  HOSortHelper::HOTerm hotermr = HOSortHelper::HOTerm(tsRght.term);  

  if(hoterml.head.isVar() && !hoterml.argnum()){
    Transform trs(ELIMINATE,FIRST);
    up.transformsLeft.push(trs);
    return;        
  }
  if(hotermr.head.isVar() && !hotermr.argnum()){
    Transform trs(ELIMINATE,SECOND);
    up.transformsLeft.push(trs);
    return;        
  }  
  
  if(hoterml.head.isVar()){
    if(hoterml.argnum() <= hotermr.argnum()){
      Transform trs(SPLIT,FIRST);
      up.transformsLeft.push(trs);       
    }
    //KX_NARROW admissable as long as var has a single argument
    Transform trs(KX_NARROW,FIRST);
    up.transformsLeft.push(trs);    
    
    if(hoterml.nthArgSort(0) == hoterml.sortOfLengthNPref(1)){
      Transform trs(I_NARROW,FIRST);
      up.transformsLeft.push(trs);       
    }
    
    if(hoterml.argnum() > 1 && (hoterml.nthArgSort(0) == hoterml.sortOfLengthNPref(2))){
      Transform trs(K_NARROW,FIRST);
      up.transformsLeft.push(trs);       
    }    
    
    if(hoterml.argnum() > 2)
      unsigned sort1 = hoterml.nthArgSort(0);
      unsigned sort2 = hoterml.nthArgSort(1);
      unsigned sort3 = hoterml.nthArgSort(2);
      if(!(HSH::arity(sort1) < 1) && !(HSH::arity(sort2) < 1)){
        
      }
      
      (HSH::domain(hoterml.nthArgSort(0)) == HSH::range(hoterml.nthArgSort(1))) &&
      (HSH::domain(hoterml.nthArgSort(1)) == hoterml.nthArgSort(2)) &&
      (HSH::range(hoterml.nthArgSort(0)) == hoterml.sortOfLengthNPref(3))){
      Transform trs(B_NARROW,FIRST);
      up.transformsLeft.push(trs);       
    }
    
    if(hoterml.argnum() > 1 && 
      (HSH::domain(hoterml.nthArgSort(0)) == hoterml.nthArgSort(1))){
      Transform trs(BX_NARROW,FIRST);
      up.transformsLeft.push(trs);
      Transform trs(SX_NARROW,FIRST);
      up.transformsLeft.push(trs);      
    }
    
    if(hoterml.argnum > 2 &&
      (HSH::appliedToN(hoterml.nthArgSort(0), 2) == hoterml.sortOfLengthNPref(3)) &&
      (hoterml.nthArgSort(1) == hoterml.nthArgSort(2)) &&
      (HSH::getNthArgSort(hoterml.nthArgSort(0), 0) == hoterml.nthArgSort(1)) &&
      (HSH::getNthArgSort(hoterml.nthArgSort(0), 1) == hoterml.nthArgSort(1))){
      Transform trs(C_NARROW,FIRST);
      up.transformsLeft.push(trs);     
    }
    
    if(hoterml.argnum() > 1 && 
      (hoterml.nthArgSort(0) == hoterml.nthArgSort(1)){
      Transform trs(CX_NARROW,FIRST);
      up.transformsLeft.push(trs);       
    }    

    if(hoterml.argnum > 2 &&
      (HSH::appliedToN(hoterml.nthArgSort(0), 2) == hoterml.sortOfLengthNPref(3)) &&
      (HSH::domain(hoterml.nthArgSort(0)) == hoterml.nthArgSort(2)) &&
      (HSH::domain(hoterml.nthArgSort(1)) == hoterml.nthArgSort(2))
      (HSH::getNthArgSort(hoterml.nthArgSort(0), 1) == HSH::range(hoterml.nthArgSort(1)))){
      Transform trs(S_NARROW,FIRST);
      up.transformsLeft.push(trs);     
    }    
    
  }
  
  
  /*
  
  if(headl.isVar()){
    if(argnuml >= argnumr){
      Transform trs(SPLIT,FIRST);
      up.transformsLeft.push(trs); 
    }    

    //KX_NARROW admissable as long as var has a single argument
    Transform trs(KX_NARROW,FIRST);
    up.transformsLeft.push(trs);   
    
    unsigned firstargsort = HOSortHelper::getnthArgSort(tsLeft.term,1);
    unsigned varappliedsort = HOSortHelper::appliedToN(headl,1);
    if(firstargsort == varappliedsort){
      Transform trs(I_NARROW,FIRST);
      up.transformsLeft.push(trs);      
    }
  }
  
  if(headr.isVar()){
    if(argnumr >= argnuml){
      Transform trs(SPLIT,SECOND);
  	  up.transformsRight.push(trs);
    }
  }  
  
  int as = isComb(headl, argnuml);

  if(as > 1){
  	Transform trs((AlgorithmStep)as,FIRST);
  	up.transformsLeft.push(trs);
  } 
  
  as = isComb(headr, arityr);
  
  if(as > 1) {
  	Transform trs((AlgorithmStep)as,SECOND);
  	up.transformsRight.push(trs);    
  }
  */
}
 
/**
  * Returns 0 if not a combinator, 1 if is combinator not fully applied
  * and the relavant AlgorithmStep otherwise 
  * @author Ahmed Bhayat
  * @location Manchester
  */
int CombSubstitution::isComb(TermList tl, unsigned arity) const
{

  CALL("CombSubstitution::isComb");

  if(tl.isVar()){ return 0; }
  SS* sym = env.signature->getFunction(tl.term()->functor());
  switch(sym->getConst()){
    case SS::I_COMB:
      return arity >= 1 ? I_REDUCE : 1;
    case SS::K_COMB:
      return arity >= 2 ? K_REDUCE : 1;
    case SS::B_COMB:
      return arity >= 3 ? B_REDUCE : 1;
    case SS::C_COMB:
      return arity >= 3 ? C_REDUCE : 1;
    case SS::S_COMB:
      return arity >= 3 ? S_REDUCE : 1;
    default:
      return 0;      
  }
}

}