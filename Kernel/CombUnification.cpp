
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

//really this ought to be a function of UnificationPair
//also should split into populateleft and populateright
void CombSubstitution::populateTransformations(UnificationPair& up)
{
  CALL("CombSubstitution::populateTransformations");

  TTPair ttpair = up.unifPair;

  HSH::HOTerm hoterml = ttpair.first.first;
  HSH::HOTerm hotermr = ttpair.second.first;   

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

  if(hoterml.varHead() && hoterml.argnum() > 0 && 
    (hoterml.argnum() <= hotermr.argnum())){
    Transform trs(SPLIT,FIRST);
    up.transformsLeft.push(trs);       
  }

  if(hotermr.varHead() && hotermr.argnum() > 0 &&  
    (hotermr.argnum() <= hoterml.argnum())){
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
    AlgorithmStep as = reduceStep(hoterm);
    Transform trs(as,at);
    tStack.push(trs);  
  }

}

CombSubstitution::AlgorithmStep CombSubstitution::reduceStep(HSH::HOTerm ht){
  CALL("CombSubstitution::reduceStep");

  SS::HOLConstant comb = ht.headComb();
  switch(comb){
    case SS::I_COMB:
      return I_REDUCE;
    case SS::K_COMB:
      return K_REDUCE;
    case SS::B_COMB:
      return B_REDUCE;
    case SS::C_COMB:
      return C_REDUCE;
    case SS::S_COMB:
      return S_REDUCE;
    default:
      ASSERTION_VIOLATION;      
  }
}

bool CombSubstitution::transform(Transform t){
  CALL("CombSubstitution::transform");

  BacktrackData localBD;
  bdRecord(localBD);

  bdAdd(new StackBacktrackObject(this, _unificationPairs));

  UnificationPair up = _unificationPairs.pop();
  HOTermSpec hts1 = up.unifPair.first;
  HOTermSpec hts2 = up.unifPair.second;
  HSH::HOTerm terml = hts1.first;
  HSH::HOTerm termr = hts2.first;
  int id1 = hts1.second;
  int id2 = hts2.second;
  //need to deal with indices.

  if(t.second == BOTH){
    ASS((t.first == ADD_ARG) || (t.first == DECOMP));
    
    if(t.first == ADD_ARG){
      unsigned freshArgSort = HSH::domain(terml.sort());
      HSH::HOTerm fc = HSH::HOTerm(TermList(Term::createFreshConstant("f", freshArgSort)));
      terml.addArg(fc);
      termr.addArg(fc);
      UnificationPair newup = UnificationPair(make_pair(terml, id1), 
                                              make_pair(termr, id2), ADD_ARG, up.lastStep);
      populateTransformations(newup);
      _unificationPairs.push(newup);
      return true;
    }

    if(t.first == DECOMP){
      ASS(terml.sameFirstOrderHead(termr));    
      HSH::HOTerm tl, tr;
      for(unsigned i = 0; i < terml.argnum(); i++){
        tl = terml.ntharg(i);
        tr = termr.ntharg(i);
        if(tl.diffFirstOrderHead(tr)){ return false; }
        UnificationPair newup = UnificationPair(make_pair(tl,id1),
                                                make_pair(tr,id2), DECOMP, up.lastStep);
        populateTransformations(newup);
        _unificationPairs.push(newup);
      }
      return true;
    }
  }

  //carry out eliminate transform
  if(t.first == ELIMINATE){
    VarSpec vs;
    HOTermSpec hts;
    vs = t.second == FIRST ? VarSpec(terml.head.var(), id1) : VarSpec(termr.head.var(), id2);
    hts = t.second == FIRST ? hts2 : hts1;  
    if(occurs(vs, hts)){
      return false;
    }
    eliminate(vs,hts.first);
    addToSolved(vs, hts.first);
  }

  //split here so we can check early for failure
  if(t.first == SPLIT){
    HOTermSpec toSplit, other;
    toSplit = t.second == FIRST ? hts1 : hts2; 
    other = t.second == FIRST ? hts2 : hts1; 
    VarSpec vs(toSplit.first.head.var(), toSplit.second);
    if(occurs(vs, other)){
      return false;
    }
    HSH::HOTerm ht = HSH::HOTerm(other.first.head);
    for(unsigned i = 0; i < other.first.argnum() - toSplit.first.argnum(); i ++){
      ht.addArg(other.first.ntharg(0));
    }
    toSplit.first.headify(ht);
    eliminate(vs,ht);
    addToSolved(vs, ht);
    //For now, the below is OK, but once I attempt to re-use 
    //algorithm steps, the order of the new pair will be important
    UnificationPair newup = UnificationPair(toSplit, other, SPLIT, up.lastStep);
    populateTransformations(newup);
    _unificationPairs.push(newup);
    return true;
  }

  if(t.second == FIRST){
    transform(terml,t.first, id1);
  } else {
    transform(termr,t.first, id2);
  }
  //test for failure 

  if(_unificationPairs.isEmpty()){
    _solved = true;
  }
  return true;

}

void CombSubstitution::transform(HSH::HOTerm& term,AlgorithmStep as, int ind){
  CALL("CombSubstitution::transform");

  if(as == I_REDUCE){
    ASS(term.headComb() == SS::I_COMB);
    iRdeuce(term);
  }

  if(as == K_REDUCE){
    ASS(term.headComb() == SS::K_COMB);
    ASS(term.argnum() > 1);
    kReduce(term);
  }

  if(as == B_REDUCE || as == C_REDUCE || as == S_REDUCE){
    ASS(term.argnum() > 2);
    bcsReduce(term,as);
  }

  if(as == I_NARROW){
    ASS(term.varHead());
    iRdeuce(term);
  }

  if(as == K_NARROW){
    ASS(term.varHead());
    kReduce(term);
  }

  if(as == B_NARROW || as == C_NARROW || as == S_NARROW){
    ASS(term.varHead());
    bcsReduce(term, as);
  }

  auto convert = [] (AlgorithmStep as) { 
    switch(as){
      case I_NARROW:
        return SS::I_COMB;
      case K_NARROW:
      case KX_NARROW:
        return SS::K_COMB;
      case B_NARROW:
      case BX_NARROW:
        return SS::B_COMB;
      case C_NARROW:
      case CX_NARROW:
        return SS::C_COMB;
      case S_NARROW:
      case SX_NARROW:
        return SS::S_COMB;
      default:
        ASSERTION_VIOLATION;
    }
  };
 
  HSH::HOTerm newvar;
  auto getNewVarSort = [] (AlgorithmStep as, HSH::HOTerm tm) { 
    unsigned range =  tm.sortOfLengthNPref(2);
    unsigned s1 = tm.nthArgSort(0);
    if(!(as == CX_NARROW)){ s1 = HSH::range(s1); }
    unsigned s0 = tm.nthArgSort(1);
    unsigned newVarSort = env.sorts->addFunctionSort(s1, range);
    if(!(as == BX_NARROW)){
      newVarSort = env.sorts->addFunctionSort(s0, newVarSort);
    }
    return newVarSort;
  };

  if(as == KX_NARROW){
    ASS(term.varHead());
    ASS(term.argnum() > 0);;
    newvar = newVar(term.sortOfLengthNPref(1));
    term.args.push_front(newvar);
    kReduce(term);
  }
   
  if(as == BX_NARROW || as == CX_NARROW || as == SX_NARROW){
    ASS(term.varHead());
    ASS(term.argnum() > 1);
    newvar = newVar(getNewVarSort(as, term));
    term.args.push_front(newvar);    
    bcsReduce(term, as);
  }  

  if(as >= I_NARROW && as <= SX_NARROW){
    HSH::HOTerm ht = HSH::HOTerm(HSH::getCombTerm(convert(as), term.headsort));
    VarSpec vs = VarSpec(term.head.var(), ind);
    if(as == KX_NARROW || as == BX_NARROW || 
       as == CX_NARROW || as == SX_NARROW){
      ht.addArg(newvar);
    }
    eliminate(vs,ht);
    addToSolved(vs, ht);
  }
}

void CombSubstitution::iRdeuce(HSH::HOTerm& ht){
  CALL("CombSubstitution::iRdeuce");

  HSH::HOTerm a1 = ht.args.pop_front();
  ht.headify(a1);
}

void CombSubstitution::kReduce(HSH::HOTerm& ht){
  CALL("CombSubstitution::kReduce");

  HSH::HOTerm a1 = ht.args.pop_front();
  ht.args.pop_front();
  ht.headify(a1);
}

void CombSubstitution::bcsReduce(HSH::HOTerm& ht, AlgorithmStep as){
  CALL("CombSubstitution::bcsReduce");

  HSH::HOTerm a1 = ht.args.pop_front();
  HSH::HOTerm a2 = ht.args.pop_front();
  HSH::HOTerm a3 = ht.args.pop_front();

  if(as == B_REDUCE || as == S_REDUCE){
    a2.addArg(a3);
  }
  ht.args.push_front(a2);
  if(as == C_REDUCE || as == S_REDUCE){
    ht.args.push_front(a3);
  }
  ht.headify(a1);
}

void CombSubstitution::addToSolved(VarSpec vs, HSH::HOTerm ht){
  CALL("CombSubstitution::addToSolved");

  _solvedPairs.set(vs, ht);
 bdAdd(new BindingBacktrackObject(this, vs)); 
}

void CombSubstitution::eliminate(VarSpec vs, HSH::HOTerm ht)
{
  CALL("CombSubstitution::eliminate");

  for(unsigned i = 0; i < _unificationPairs.size(); i++){
    eliminate(vs, ht, _unificationPairs[i].unifPair.first);
    eliminate(vs, ht, _unificationPairs[i].unifPair.second);
  }
}

void CombSubstitution::eliminate(VarSpec vs, HSH::HOTerm ht, HOTermSpec& target)
{
  CALL("CombSubstitution::eliminate");

  if(vs.index != target.second){ return; }

  HSH::HOTerm* targ = &target.first;
  unsigned var = vs.index;
  Stack<HSH::HOTerm*> toDo;

  toDo.push(targ);
  while(!toDo.isEmpty()){
    targ = toDo.pop();
    if(targ->head.isVar() && (targ->head.var() == var)){
      targ->headify(ht);
      //If headification has resulted in a weak redex reduce it
      if(targ->combHead() && !targ->underAppliedCombTerm()){
        AlgorithmStep as = reduceStep(*targ);
        transform(*targ, as, target.second);
      }
    }
    for(unsigned i = 0; i < targ->argnum(); i++){
      toDo.push(targ->nthargptr(i));
    }
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

bool CombSubstitution::occurs(VarSpec vs, HOTermSpec hts){
  CALL("CombSubstitution::occurs");

  if(!(vs.index == hts.second)){
    return false;
  }
  HSH::HOTerm ht = hts.first;
  unsigned var = vs.index;
  Stack<HSH::HOTerm> toDo;

  toDo.push(ht);
  while(!toDo.isEmpty()){
    ht = toDo.pop();
    if(ht.head.isVar() && (ht.head.var() == var)){
      return true;
    }
    for(unsigned i = 0; i < ht.argnum(); i++){
      toDo.push(ht.ntharg(i));
    }
  }
  return false;
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