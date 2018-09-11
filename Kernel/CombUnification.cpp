
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
#include "Lib/DHSet.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"

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


CombSubstitution::TransformIterator CombSubstitution::availableTransforms()
{
  CALL("CombSubstitution::availableTransforms");

  UnificationPair up = _unificationPairs.top();

  Stack<Transform>::Iterator both(up.transformsBoth);
  Stack<Transform>::Iterator left(up.transformsLeft);
  Stack<Transform>::Iterator right(up.transformsRight);

  auto it = getConcatenatedIterator(left, right);

  return pvi(getConcatenatedIterator(both, it));

}

//really this ought to be a function of UnificationPair;
void CombSubstitution::populateTransformations(UnificationPair& up)
{
  CALL("CombSubstitution::populateTransformations");

  TTPair ttpair = up.unifPair;

  HSH::HOTerm hoterml = ttpair.first;
  HSH::HOTerm hotermr = ttpair.second;   

  if(hoterml.isVar()){
    Transform trs(ELIMINATE,FIRST);
    up.transformsLeft.push(trs);
    return;        
  }
  // if unification is between two variables arbitrarily choose to eliminate
  // left of pair
  if(hotermr.isVar() && !hoterml.isVar()){
    Transform trs(ELIMINATE,SECOND);
    up.transformsRight.push(trs);
    return;        
  }  

  if(hoterml.varHead() && (hoterml.argnum() <= hotermr.argnum())){
    Transform trs(SPLIT,FIRST);
    up.transformsLeft.push(trs);       
  }

  if(hotermr.varHead() && (hotermr.argnum() <= hoterml.argnum())){
    Transform trs(SPLIT,SECOND);
    up.transformsRight.push(trs);       
  }

  populateSide(hoterml, FIRST, up.transformsLeft, up.lastStep, up.secondLastStep);
  populateSide(hoterml, SECOND, up.transformsRight, up.lastStep, up.secondLastStep);

  if(hoterml.sameFirstOrderHead(hotermr)){
    Transform trs(DECOMP,BOTH);
    up.transformsBoth.push(trs);      
  }
  
  if(hoterml.underAppliedCombTerm() || hoterml.underAppliedCombTerm()){
    Transform trs(ADD_ARG,BOTH);
    up.transformsBoth.push(trs); 
  }

}

//not sure about tStack. Will changes to it be local?
void CombSubstitution::populateSide(HSH::HOTerm hoterm, ApplyTo at, Stack<Transform>& tStack,
                                    AlgorithmStep ls, AlgorithmStep sls){
  CALL("CombSubstitution::populateSide");

  if(hoterm.varHead()){
    //KX_NARROW admissable as long as var has a single argument
    if(canPerformStep(ls,sls, KX_NARROW)){
      Transform trs(KX_NARROW,at);
      tStack.push(trs);    
    }
    
    if(hoterm.nthArgSort(0) == hoterm.sortOfLengthNPref(1)){
      if(canPerformStep(ls,sls,I_NARROW)){
        Transform trs(I_NARROW,at);
        tStack.push(trs); 
      }      
    }
    
    if(hoterm.argnum() > 1 && (hoterm.nthArgSort(0) == hoterm.sortOfLengthNPref(2))){
      if(canPerformStep(ls, sls, K_NARROW)){
        Transform trs(K_NARROW,at);
        tStack.push(trs);
      }       
    }    
    
    if(hoterm.argnum() > 2){
      unsigned sort1 = hoterm.nthArgSort(0);
      unsigned sort2 = hoterm.nthArgSort(1);
      unsigned sort3 = hoterm.nthArgSort(2);
      //B narrow  
      if(!(HSH::arity(sort1) < 1) && !(HSH::arity(sort2) < 1)){
        if((HSH::domain(sort1) == HSH::range(sort2) &&
           (HSH::domain(sort2) == sort3) &&
           (HSH::range(sort1) == hoterm.sortOfLengthNPref(3)))){
          Transform trs(B_NARROW,at);
          tStack.push(trs);
        }        
      }
      //C narrow
      if(!(HSH::arity(sort1) < 2)){
        if((HSH::appliedToN(sort1, 2) == hoterm.sortOfLengthNPref(3)) &&
           (HSH::getNthArgSort(sort1, 0) == sort2) &&
           (HSH::getNthArgSort(sort1, 1) == sort3)){
          Transform trs(C_NARROW,at);
          tStack.push(trs); 
        }
      }
      //S narrow
      if(!(HSH::arity(sort1) < 2) && !(HSH::arity(sort2) < 1)){
        if((HSH::appliedToN(sort1, 2) == hoterm.sortOfLengthNPref(3)) &&  
           (HSH::domain(sort1) == sort3) &&
           (HSH::domain(sort2) == sort3) &&
           (HSH::getNthArgSort(sort1, 1) == HSH::range(sort2))){
          Transform trs(S_NARROW,at);
          tStack.push(trs);           
        }
      }
    }
    
    if(hoterm.argnum() > 1){
      unsigned sort1 = hoterm.nthArgSort(0);
      unsigned sort2 = hoterm.nthArgSort(1);
      if(!(HSH::arity(sort1) < 1)){
        if(HSH::domain(sort1) == sort2){
          Transform trs(BX_NARROW,at);
          tStack.push(trs);
          Transform trs2(SX_NARROW,at);
          tStack.push(trs2);
        }
      }
      if(canPerformStep(ls, sls, CX_NARROW)){
        Transform trs(CX_NARROW,at);
        tStack.push(trs);
      }          
    } 

  }

  if(hoterm.combHead() && !hoterm.underAppliedCombTerm()){
    AlgorithmStep as;
    SS::HOLConstant comb = hoterm.headComb();
    switch(comb){
      case SS::I_COMB:
        as = I_REDUCE;
        break;
      case SS::K_COMB:
        as = K_REDUCE;
        break;
      case SS::B_COMB:
        as = B_REDUCE;
        break;
      case SS::C_COMB:
        as = C_REDUCE;
        break;
      case SS::S_COMB:
        as = S_REDUCE;
        break;
      default:
        ASSERTION_VIOLATION;      
    }
    Transform trs(as,at);
    tStack.push(trs);  
  }

}

bool CombSubstitution::transform(Transform t){
  CALL("CombSubstitution::transform");

  BacktrackData localBD;
  bdRecord(localBD);

  bdAdd(new StackBacktrackObject(this, _unificationPairs));

  UnificationPair up = _unificationPairs.pop();
  HSH::HOTerm terml = up.unifPair.first;
  HSH::HOTerm termr = up.unifPair.second;

  if(t.second == BOTH){
    ASS((t.first == ADD_ARG) || (t.first == DECOMP));
    
    if(t.first == ADD_ARG){
      unsigned freshArgSort = HSH::domain(terml.sort());
      TermList fc = TermList(Term::createFreshConstant("f", freshArgSort));
      terml.args.push_back(fc);
      terml.sorts.push_back(freshArgSort);
      termr.args.push_back(fc);
      termr.sorts.push_back(freshArgSort);
      UnificationPair newup = UnificationPair(terml, termr, ADD_ARG, up.lastStep);
      populateTransformations(newup);
      _unificationPairs.push(newup);
      return true;
    }

    if(t.first == DECOMP){
      ASS(terml.sameFirstOrderHead(termr));    
      HSH::HOTerm tl, tr;
      for(unsigned i = 0; i < terml.argnum(); i++){
        tl = HSH::HOTerm(terml.ntharg(i), terml.index);
        tr = HSH::HOTerm(termr.ntharg(i), terml.index);
        if(tl.diffFirstOrderHead(tr)){
          return false;
        }
        UnificationPair newup = UnificationPair(tl, tr, DECOMP, up.lastStep);
        populateTransformations(newup);
        _unificationPairs.push(newup);
      }
      return true;
    }
  }
  //carry out eliminate transform

  //split here so we can check early for failure

  if(t.second == FIRST){
    transform(terml,t.first);
  } else {
    transform(termr,t.first);
  }
  //test for failure 

}

void CombSubstitution::transform(HSH::HOTerm& term,AlgorithmStep as){
  CALL("CombSubstitution::transform");

  TermList a1, a2, a3;
  unsigned s1, s2, s3;

  if(as == I_REDUCE){
    ASS(term.headComb() == SS::I_COMB);
    a1 = term.args.pop_front();
    s1 = term.sorts.pop_front();
    term.headify(a1, s1);
    return;
  }

  if(as == K_REDUCE){
    ASS(term.headComb() == SS::K_COMB);
    ASS(term.argnum() > 1);
    a1 = term.args.pop_front();
    s1 = term.sorts.pop_front();
    term.args.pop_front();
    term.sorts.pop_front();
    term.headify(a1, s1);
    return;
  }

  if(as == B_REDUCE || as == C_REDUCE || as == S_REDUCE){
    a1 = term.args.pop_front();
    s1 = term.sorts.pop_front();
    a2 = term.args.pop_front();
    s2 = term.sorts.pop_front();
    a3 = term.args.pop_front();
    s3 = term.sorts.pop_front();
  }

  if(as == B_REDUCE){
    ASS(term.headComb() == SS::B_COMB);
    ASS(term.argnum() > 2);
    term.args.push_front(HSH::apply(a2, s2, a3, s3));
    term.sorts.push_front(HSH::range(s2));
    term.headify(a1, s1);
    return;
  }

  if(as == C_REDUCE){
    ASS(term.headComb() == SS::C_COMB);
    ASS(term.argnum() > 2);
    term.args.push_front(a2);
    term.sorts.push_front(s2);
    term.args.push_front(a3);
    term.sorts.push_front(s3);
    term.headify(a1, s1);
    return;
  }

  if(as == S_REDUCE){
    ASS(term.headComb() == SS::S_COMB);
    ASS(term.argnum() > 2);
    term.args.push_front(HSH::apply(a2, s2, a3, s3));
    term.sorts.push_front(HSH::range(s2));
    term.args.push_front(a3);
    term.sorts.push_front(s3);
    term.headify(a1, s1);
    return;
  }


}

bool CombSubstitution::canPerformStep(AlgorithmStep ls, AlgorithmStep sls, AlgorithmStep curr){
  CALL("CombSubstitution::canPerformKXStep");
  switch(curr){
    case KX_NARROW:
      return (!(ls == SX_NARROW) && !(ls == BX_NARROW) && 
              !(ls == CX_NARROW && sls == SX_NARROW) &&
              !(ls == KX_NARROW && sls == CX_NARROW));
    case K_NARROW:
      return (!(ls == SX_NARROW) && !(ls == CX_NARROW));
    case I_NARROW:
      return  (!(ls == BX_NARROW) && !(ls == KX_NARROW && sls == CX_NARROW)); 
    case CX_NARROW:
      return !(ls == CX_NARROW);   
    default:
      return true; 
  }
}

//need to comment this code AYB
bool CombUnification::hasNextUnifier(){
  CALL("CombUnification::hasNextUnifier");

  if(_unifSystem->_solved) {
    bdStack.pop().backtrack();
    _unifSystem->_solved=false;
  }  

  ASS(bdStack.length()+1==transformIterators.length());

  do {
    while(!transformIterators.top().hasNext() && !bdStack.isEmpty()) {
      bdStack.pop().backtrack();
    }
    if(!transformIterators.top().hasNext()) {
      return false;
    }
    Transform t=transformIterators.top().next();

    BacktrackData bd;
    bool success=transform(t,bd);
    if(!success) {
      bd.backtrack();
      continue;
    } else {
      bdStack.push(bd);
    }
  } while(!_unifSystem->_solved);
  return true;
}

bool CombUnification::transform(Transform t, BacktrackData& bd){
  CALL("CombUnification::transform");

  _unifSystem->bdRecord(bd);

  bool success = _unifSystem->transform(t);
  if(success){
    if(!_unifSystem->_solved){
      TransformIterator ti = _unifSystem->availableTransforms();
      transformIterators.backtrackablePush(ti, bd);
    }
  }
  _unifSystem->bdDone();
  return success;
}



}