
/*
 * File CombSubstIterator.cpp.
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
 * @file CombSubstIterator.cpp
 */

#include "Lib/Environment.hpp"

#include "SortHelper.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Signature.hpp"
#include "HOSortHelper.hpp"

#include "CombSubstIterator.hpp"

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

Stack<CombSubstitution::Transform> CombSubstitution::availableTransforms()
{
  CALL("CombSubstitution::availableTransforms");

  ASS(_mode == RESTRICTED || !_solved);

  //if running in full mode, no transforms are carried out on flex-flex paris
  if(_mode == FULL){
    unsigned size = _unificationPairs.size();
    unsigned i = size - 1;
    while(_unificationPairs[i].isFlexFlex()){ i--; } 
    //loop cannot be infinite because if all pairs were flex-flex system would be solved
    if(i != (size - 1)){
      //swap
      UnificationPair temp = _unificationPairs[size - 1];
      _unificationPairs[size - 1] = _unificationPairs[i];
      _unificationPairs[i] = temp;
    }
  }

  populateTransformations(_unificationPairs.top());

  UnificationPair up = _unificationPairs.top();

  TransformStack left = up.transformsLeft;
  TransformStack right = up.transformsRight;
  TransformStack both = up.transformsBoth;
 
  if(!both.isEmpty()){
    return both;
  } else {
    if(_mode == FULL){
      ASS(right.isEmpty() || left.isEmpty());
      while(!right.isEmpty()){
        both.push(right.pop()); //easy way to circumvent checking which is non-empty
      }
      while(!left.isEmpty()){
        both.push(left.pop());
      }
      return both;
    }
    while(!right.isEmpty()){
      left.push(right.pop());
    }
    return left;
  }
}

//really this ought to be a function of UnificationPair
//also should split into populateleft and populateright
void CombSubstitution::populateTransformations(UnificationPair& up)
{
  CALL("CombSubstitution::populateTransformations");

  HOTerm_ptr hoterml = up.terml;
  HOTerm_ptr hotermr = up.termr;   

  ASS_REP(hoterml->srt == hotermr->srt, 
          "hoterml " + hoterml->toStringWithTopLevelSorts() +
          "hotermr " + hotermr->toStringWithTopLevelSorts());
  ASS(systemIsWellSorted());
  ASS(_mode == RESTRICTED || !up.isFlexFlex());

  //cout << "terml is " + hoterml->toString(false, true) << endl;
  //cout << "termr is " + hotermr->toString(false, true) << endl;

  //true here means that indices are used in the comparison
  if(HSH::equal(hotermr, hoterml, true)){
    Transform trs = Transform(ID,BOTH);
    up.transformsLeft.push(trs);
    return;  
  }

  if(hoterml->isVar()){
    Transform trs = Transform(ELIMINATE,FIRST);
    up.transformsLeft.push(trs);
    return;        
  }
  
  // if unification is between two variables arbitrarily choose to eliminate
  // left of pair
  if(hotermr->isVar() && !hoterml->isVar()){
    Transform trs = Transform(ELIMINATE,SECOND);
    up.transformsRight.push(trs);
    return;        
  }  

  if(hoterml->sameFirstOrderHead(hotermr)){
    ASS_REP(hoterml->argnum() == hotermr->argnum(),
      hoterml->toStringWithTopLevelSorts() + "\n" + 
      hotermr->toStringWithTopLevelSorts())
    Transform trs = Transform(DECOMP,BOTH);
    up.transformsBoth.push(trs);
    return;      
  }
  
  if(hoterml->underAppliedCombTerm() || hotermr->underAppliedCombTerm()){
    Transform trs = Transform(ADD_ARG,BOTH);
    up.transformsBoth.push(trs);
    return; 
  }

  if(hoterml->combHead() && !hoterml->underAppliedCombTerm()){
    AlgorithmStep as = reduceStep(hoterml);
    Transform trs = Transform(as,FIRST);
    up.transformsLeft.push(trs);
    return;  
  } else if(hotermr->combHead() && !hotermr->underAppliedCombTerm()){
    AlgorithmStep as = reduceStep(hotermr);
    Transform trs = Transform(as,SECOND);
    up.transformsRight.push(trs);
    return;
  }

  int diff = hoterml->argnum() - hotermr->argnum();
  
  if(hoterml->isAppliedVar() && diff <= 0 &&
    !hoterml->sameVarHead(hotermr,true)){
    TypeSub* ts = new TypeSub();
    if(isUnifiable(hoterml->headsort, hotermr->sortOfLengthNPref(abs(diff)), ts)){
      Transform trs = Transform(SPLIT,FIRST,ts);
      up.transformsLeft.push(trs);
    }       
  }

  if(hotermr->isAppliedVar()                        &&  
    (diff > 0|| (diff == 0 && !hoterml->varHead())) &&
    !hotermr->sameVarHead(hoterml,true)){
    TypeSub* ts  = new TypeSub();
    if(isUnifiable(hotermr->headsort, hoterml->sortOfLengthNPref(diff),ts)){
      Transform trs = Transform(SPLIT,SECOND, ts);
      up.transformsRight.push(trs);
    }       
  }

  PairType pt = up.getPairType();
  if(pt == FLEX_FLEX_SAME_HEAD){
    //If both sides have the same variable head (flex-flex) then a change on one
    //side will automatically take place on the other via eliminate
    populateSide(hoterml, FIRST, up.transformsLeft, up.lsLeft, up.slsLeft);
  }else if(pt == FLEX_FLEX_DIFF_HEAD && up.mostRecentSide == SECOND){
    //Once transformations are carried out on the right, cannot swap
    //back to left
     populateSide(hotermr, SECOND, up.transformsRight, up.lsRight, up.slsRight);
  }else if(pt == FLEX_FLEX_DIFF_HEAD){
    populateSide(hoterml, FIRST, up.transformsLeft, up.lsLeft, up.slsLeft);
    populateSide(hotermr, SECOND, up.transformsRight, up.lsRight, up.slsRight);
  }else if (pt == FLEX_RIGID_LEFT && 
    //preventing a move back to left
    !(up.mostRecentSide == SECOND && up.lsRight >= I_NARROW && up.lsRight <= SX_NARROW)){
    populateSide(hoterml, FIRST, up.transformsLeft, up.lsLeft, up.slsLeft);
  }else if (pt == FLEX_RIGID_RIGHT){
    populateSide(hotermr, SECOND, up.transformsRight, up.lsRight, up.slsRight);
  }

}

void CombSubstitution::populateSide(const HOTerm_ptr hoterm, ApplyTo at, TransformStack& tStack,
                                    AlgorithmStep ls, AlgorithmStep sls){
  CALL("CombSubstitution::populateSide");

  //cout << "Populating for term " + hoterm->toStringWithTopLevelSorts() << endl;

  ASS(hoterm->varHead());
  //KX_NARROW admissable as long as var has a single argument
  if(canPerformStep(ls,sls, KX_NARROW)){
    Transform trs = Transform(KX_NARROW,at);
    tStack.push(trs);    
  }
  
  TypeSub* ts = new TypeSub();
  if(isUnifiable(hoterm->nthArgSort(0), hoterm->sortOfLengthNPref(1), ts)){
    if(canPerformStep(ls,sls,I_NARROW)){
      Transform trs = Transform(I_NARROW,at,ts);
      tStack.push(trs); 
    }      
  }
 
  ts = new TypeSub();
  if(hoterm->argnum() > 1 &&
     isUnifiable(hoterm->nthArgSort(0), hoterm->sortOfLengthNPref(2), ts)){
    if(canPerformStep(ls, sls, K_NARROW)){
      Transform trs = Transform(K_NARROW,at,ts);
      tStack.push(trs);
    }       
  }

  //problems here when working in FULL mode...
  //type unification is far from being general enough at the moment
  if(hoterm->argnum() > 2){
    unsigned sort1 = hoterm->nthArgSort(0);
    unsigned sort2 = hoterm->nthArgSort(1);
    unsigned sort3 = hoterm->nthArgSort(2);
    //B narrow  
    if(!(HSH::arity(sort1) < 1) && !(HSH::arity(sort2) < 1)){
      ts = new TypeSub();
      if((isUnifiable(HSH::domain(sort1), HSH::range(sort2), ts) &&
         (isUnifiable(HSH::domain(sort2), sort3, ts)) &&
         (isUnifiable(HSH::range(sort1), hoterm->sortOfLengthNPref(3), ts)))){
        Transform trs = Transform(B_NARROW,at,ts);
        tStack.push(trs);
      }        
    }
    //C narrow
    if(!(HSH::arity(sort1) < 2)){
      ts = new TypeSub();
      if((isUnifiable(HSH::appliedToN(sort1, 2), hoterm->sortOfLengthNPref(3), ts)) &&
         (isUnifiable(HSH::getNthArgSort(sort1, 0), sort3, ts)) &&
         (isUnifiable(HSH::getNthArgSort(sort1, 1), sort2, ts))){
        Transform trs = Transform(C_NARROW,at,ts);
        tStack.push(trs); 
      }
    }
    //S narrow
    if(!(HSH::arity(sort1) < 2) && !(HSH::arity(sort2) < 1)){
      ts = new TypeSub();
      if((isUnifiable(HSH::appliedToN(sort1, 2), hoterm->sortOfLengthNPref(3), ts)) &&  
         (isUnifiable(HSH::domain(sort1), sort3, ts)) &&
         (isUnifiable(HSH::domain(sort2), sort3, ts)) &&
         (isUnifiable(HSH::getNthArgSort(sort1, 1), HSH::range(sort2), ts) )){
        Transform trs = Transform(S_NARROW,at,ts);
        tStack.push(trs);           
      }
    }
  }

  if(hoterm->argnum() > 1 && _mode == RESTRICTED){
    unsigned sort1 = hoterm->nthArgSort(0);
    unsigned sort2 = hoterm->nthArgSort(1);
    if(HSH::arity(sort1)){
      if(HSH::domain(sort1) == sort2){
        Transform trs = Transform(BX_NARROW,at);
        tStack.push(trs);
        Transform trs2 = Transform(SX_NARROW,at);
        tStack.push(trs2);
      }
    }
    if(canPerformStep(ls, sls, CX_NARROW)){
      Transform trs = Transform(CX_NARROW,at);
      tStack.push(trs);
    }          
  } 

  if(hoterm->argnum() > 1 && _mode == FULL && _xNarrowSteps < MAX_DEPTH_BOUND){
    ts = new TypeSub();
    unsigned sort1 = hoterm->nthArgSort(0);
    unsigned sort2 = hoterm->nthArgSort(1);
    unsigned sortVar = HSH::freshSortVar();
    sort2 = HSH::addFuncSort(sort2, sortVar);
 
    if(isUnifiable(sort1, sort2, ts)){
      Transform trs = Transform(BX_NARROW,at,ts);
      tStack.push(trs);
      TypeSub* ts2 = new TypeSub(ts);
      Transform trs2 = Transform(SX_NARROW,at,ts2);
      tStack.push(trs2);
    }
  
    if(canPerformStep(ls, sls, CX_NARROW)){
      Transform trs = Transform(CX_NARROW,at); //no need for type sub
      tStack.push(trs);
    }          
  } 


  if(hoterm->argnum() && _mode == FULL && _xxNarrowSteps < MAX_DEPTH_BOUND){
    //SX'X'' etc. narrow steps.
    //Steps are totally unconstrained by typing considerations
    Transform trs = Transform(BXX_NARROW,at);
    tStack.push(trs);

    Transform trs2 = Transform(CXX_NARROW,at);
    tStack.push(trs2);

    Transform trs3 = Transform(SXX_NARROW,at);
    tStack.push(trs3);
  }

}

CombSubstitution::AlgorithmStep CombSubstitution::reduceStep(const HOTerm_ptr ht) const
{
  CALL("CombSubstitution::reduceStep");

  SS::HOLConstant comb = ht->headComb();
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

bool CombSubstitution::isUnifiable(unsigned sort1, unsigned sort2, TypeSub* ts)
{
  CALL("CombSubstitution::isUnifiable");

  //add assertion that sort1 and sort2 are variable disjoint

  if(_mode == RESTRICTED){  
    if (sort1 == sort2){ return true; }
    delete ts;
    return false;
  }

  Stack<sortPair> sortPairs;
  sortPairs.push(sortPair(sort1, sort2));

  while(!sortPairs.isEmpty()){
    sortPair sp = sortPairs.pop();
    unsigned s1 = sp.first;
    unsigned s2 = sp.second;
    if(s1 == s2){
      continue;
    }else if(HSH::isFuncSort(s1) && HSH::isFuncSort(s2)){
      sortPairs.push(sortPair(HSH::domain(s1), HSH::domain(s2)));
      sortPairs.push(sortPair(HSH::range(s1), HSH::range(s2)));
    } else if(HSH::isSortVar(s1) && !HSH::occurs(s1,s2)) {
      if(ts->bind(s1, s2)){} else {
        delete ts;
        return false;
      }
    } else if(HSH::isSortVar(s2) && !HSH::occurs(s2,s1)){
      if(ts->bind(s2, s1)){} else {
        delete ts;
        return false;
      }      
    } else {
      delete ts;
      return false;
    }
  }
  return true;
}


bool CombSubstitution::transform(Transform t, bool furtherOptions){
  CALL("CombSubstitution::transform");
  
  BacktrackData localBD;
  bdRecord(localBD);

  //Only want to record existing unification pairs if there is the possibility of 
  //backtracking to them. If from existing system, the current transform is the only
  //available transform, then there is no point in recording the pairs.
  if(furtherOptions){
    bdAdd(new StackBacktrackObject(this, _unificationPairs));
  }

  UnificationPair* up = &_unificationPairs.top();
  //temporary measure, in the long run, manipulate transforms rather than emptying them.
  up->emptyTransforms();

  //cout << "carrying out transformation " + algorithmStepToString(t.algStep) << endl;
  //cout << "on unification pair" +  up->toString() << endl;

  //cout << "The substitution so far is " + toString() << endl; 
 
  HOTerm_ptr terml = up->terml;
  HOTerm_ptr termr = up->termr;

  bool succeeded = true;
  //need to deal with indices.

  if(t.algStep == ID){
    _unificationPairs.pop();
  }
  
  if(t.appTo == BOTH && t.algStep != ID){
    ASS((t.algStep == ADD_ARG) || (t.algStep == DECOMP));
    
    if(t.algStep == ADD_ARG){
      unsigned freshArgSort = HSH::domain(terml->sort());
      TermList newArg = TermList(Term::createFreshConstant("f",freshArgSort, true));
      HOTerm_ptr fcl = HSH::createHOTerm(newArg);
      HOTerm_ptr fcr = HSH::createHOTerm(newArg);
      terml->addArg(fcl);
      termr->addArg(fcr);
      up->lsRight = UNDEFINED;
      up->lsLeft = UNDEFINED;
      up->slsRight = UNDEFINED;
      up->slsLeft = UNDEFINED;
    }

    if(t.algStep == DECOMP){
      ASS(terml->sameFirstOrderHead(termr));
      _unificationPairs.pop();     
      HOTerm_ptr tl, tr; 
      for(unsigned i = 0; i < terml->argnum(); i++){
        tl = terml->ntharg(i);
        tr = termr->ntharg(i);
        if(tl->diffFirstOrderHead(tr)){ 
          succeeded = false;
          break; 
        }
        pushNewPair(tl, tr);
      }
    }
  }

  //carry out eliminate transform
  if(t.algStep == ELIMINATE){
    VarSpec vs;
    vs = t.appTo == FIRST ? VarSpec(terml->head.var(), terml->headInd) 
                           : VarSpec(termr->head.var(), termr->headInd);
    HOTerm_ptr ht = t.appTo == FIRST ? termr : terml; 
    if(occursOrNotPure(vs, ht)){
      succeeded =  false;
    } else {
      eliminate(vs, ht);
      addToSolved(vs, ht);
      _unificationPairs.pop();
    }
  }

  //split here so we can check early for failure
  if(t.algStep == SPLIT){
    HOTerm_ptr toSplit;
    HOTerm_ptr other;
    toSplit = t.appTo == FIRST ? terml : termr; 
    other = t.appTo == FIRST ? termr : terml; 
    VarSpec vs(toSplit->head.var(), toSplit->headInd);
    
    HOTerm_ptr ht = HSH::createHOTerm(other->head, other->headsort, other->headInd);
    for(unsigned i = 0; i < other->argnum() - toSplit->argnum(); i ++){
      HOTerm_ptr arg = HSH::createHOTerm(other->ntharg(i));
      ht->addArg(arg);
    }
    
    if(occursOrNotPure(vs, ht)){
      succeeded = false;
    } else {
      toSplit->headify(ht);
      //eliminate(vs, ht, toSplit);
      //eliminate(vs, ht, other);
      eliminate(vs, ht);
      addToSolved(vs, ht);    
      if(t.appTo == FIRST){
        //have made left head same as right, so make last steps on left side same as those on right
        up->lsLeft = up->lsRight;
        up->slsLeft = up->slsRight;
      } else {
        up->lsRight = up->lsLeft;
        up->slsRight = up->slsLeft;      
      }
    }
  }

  if((_mode == FULL && t.algStep == SPLIT && succeeded) ||
     (_mode == FULL && t.algStep >= I_NARROW && t.algStep <= SX_NARROW && t.algStep != KX_NARROW && t.algStep != CX_NARROW)){
    ASS(t.sub);
    applyTypSub(t.sub);
  }
  if(t.sub && !t.sub->isEmpty()){ delete t.sub; }

  if(t.algStep != SPLIT && t.algStep != ELIMINATE && t.algStep != DECOMP && t.algStep != ADD_ARG){
    if(t.appTo == FIRST){
      transform(terml, t.algStep);
      up->slsLeft = up->lsLeft;
      up->lsLeft = t.algStep;
    } else {
      transform(termr, t.algStep);
      up->slsRight = up->lsRight;
      up->lsRight = t.algStep;
    }
    up->mostRecentSide = t.appTo;
  }
   
  //cout << "at this point the substitution is " + toString() << endl;

  bdDone();
  if(!succeeded) {
    localBD.backtrack();
  } else {
    bdCommit(localBD);
    localBD.drop();
  }
  if(succeeded && succeed(_unificationPairs)){
    _solved = true;
  }
  return succeeded;

}

bool CombSubstitution::succeed(const Stack<UnificationPair>& ups)
{
  CALL("CombSubstitution::succeed");

  if(_mode == RESTRICTED){ return ups.isEmpty(); }
  
  //when working in FULL mode system is solved if it consists of
  //all flex-flex pairs
  for(unsigned i = 0; i < ups.size(); i++){
    if(!ups[i].isFlexFlex()) { return false; }
  }
  return true;
}

void CombSubstitution::transform(HOTerm_ptr term, AlgorithmStep as){
  CALL("CombSubstitution::transform2");

  //cout << "carrying out transformation with " + term->toString(false, true) << endl;

  if(as == I_REDUCE){
    ASS(term->headComb() == SS::I_COMB);
    iReduce(term);
  }

  if(as == K_REDUCE){
    ASS(term->headComb() == SS::K_COMB);
    ASS(term->argnum() > 1);
    kReduce(term);
  }

  if(as == B_REDUCE || as == C_REDUCE || as == S_REDUCE){
    ASS(term->argnum() > 2);
    bcsReduce(term,as);
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
      case BXX_NARROW:
        return SS::B_COMB;
      case C_NARROW:
      case CX_NARROW:
      case CXX_NARROW:
        return SS::C_COMB;
      case S_NARROW:
      case SX_NARROW:
      case SXX_NARROW:
        return SS::S_COMB;
      default:
        ASSERTION_VIOLATION;
    }
  };

  auto getNewVarSort = [] (AlgorithmStep as, HOTerm_ptr tm) { 
    unsigned range =  tm->sortOfLengthNPref(2);
    unsigned s1 = tm->nthArgSort(0);
    if(!(as == CX_NARROW)){ s1 = HSH::range(s1); }
    unsigned s0 = tm->nthArgSort(1);
    unsigned newVarSort = HSH::addFuncSort(s1, range);
    if(!(as == BX_NARROW)){
      newVarSort = HSH::addFuncSort(s0, newVarSort);
    }
    return newVarSort;
  };

  auto getReduceEquiv =[](AlgorithmStep as){
    switch(as){
      case B_NARROW:
      case BX_NARROW:
      case BXX_NARROW:
        return B_REDUCE;
      case C_NARROW:
      case CX_NARROW:
      case CXX_NARROW:
        return C_REDUCE;
      case S_NARROW:
      case SX_NARROW:
      case SXX_NARROW:
        return S_REDUCE;
      default:
        ASSERTION_VIOLATION;
    }
  };

  HOTerm_ptr newvar;
  HOTerm_ptr newvar2;
  unsigned oldvar = term->varHead() ? term->head.var() : 0;
  unsigned oldsort = term->headsort;
  int oldInd = term->headInd; //index may become -1 on the non X' narrow steps
  
  if(as == I_NARROW){
    ASS(term->varHead());
    iReduce(term);
  }

  if(as == K_NARROW){
    ASS(term->varHead());
    kReduce(term);
  }

  if(as == B_NARROW || as == C_NARROW || as == S_NARROW){
    ASS(term->varHead());
    bcsReduce(term, getReduceEquiv(as));
  }

  if(as == KX_NARROW){
    ASS(term->varHead());
    ASS(term->argnum() > 0);
    newvar = newVar(term->sortOfLengthNPref(1), term->headInd);
    term->args.push_front(newvar);
    kReduce(term);
  }
  
  if(as == BX_NARROW || as == CX_NARROW || as == SX_NARROW){
    ASS(term->varHead());
    ASS(term->argnum() > 1);
    _xNarrowSteps++;
    newvar = newVar(getNewVarSort(as, term), term->headInd);
    term->args.push_front(newvar);    
    bcsReduce(term, getReduceEquiv(as));
  }  

  if(as >= BXX_NARROW && as <= SXX_NARROW){
    ASS(_mode == FULL);

    _xxNarrowSteps++;
    unsigned sortVar = HSH::freshSortVar();
    unsigned range =  term->sortOfLengthNPref(1);
    unsigned s0 = term->nthArgSort(0);

    unsigned v1sort = (as != BXX_NARROW) ? HSH::addFuncSort(s0, HSH::addFuncSort(sortVar, range)) :
                                           HSH::addFuncSort(sortVar, range);
    unsigned v2sort = (as != CXX_NARROW) ? HSH::addFuncSort(s0, sortVar) : sortVar;

    newvar = newVar(v1sort, term->headInd);
    newvar2 = newVar(v2sort, term->headInd);
    term->args.push_front(HSH::createHOTerm(newvar2)); 
    term->args.push_front(newvar);     
    bcsReduce(term, getReduceEquiv(as));
  }

  if(as >= I_NARROW && as <= SXX_NARROW){
    HOTerm_ptr ht;
    VarSpec vs = VarSpec(oldvar, oldInd);
    if(as == KX_NARROW || as == BX_NARROW || as == CX_NARROW || as == SX_NARROW ||
       as == BXX_NARROW || as == CXX_NARROW  || as == SXX_NARROW){
      unsigned combSort = oldsort;       
      if(as >= BXX_NARROW && as <= SXX_NARROW){
        combSort = HSH::addFuncSort(newvar2->sort(), combSort);
      }
      combSort = HSH::addFuncSort(newvar->sort(), combSort);
      ht = HSH::createHOTerm(HSH::getCombTerm(convert(as), combSort));
      ht->addArg(newvar);
      if(as >= BXX_NARROW && as <= SXX_NARROW){
        ht->addArg(newvar2);
      }
    } else {
      ht = HSH::createHOTerm(HSH::getCombTerm(convert(as), oldsort));
    }
    //eliminate(vs, ht, term);
    //eliminate(vs, ht, other);
    eliminate(vs, ht);
    addToSolved(vs, ht);
  }

}

void CombSubstitution::iReduce(HOTerm_ptr ht) const{ 
  CALL("CombSubstitution::iReduce");

  HOTerm_ptr a1 = ht->args.pop_front();
  ht->headify(a1);
}

void CombSubstitution::kReduce(HOTerm_ptr ht) const{
  CALL("CombSubstitution::kReduce");

  HOTerm_ptr a1 = ht->args.pop_front();
  ht->args.pop_front();
  ht->headify(a1);
}

void CombSubstitution::bcsReduce(HOTerm_ptr ht, AlgorithmStep as) const{
  CALL("CombSubstitution::bcsReduce");

  //cout << "The sort of the head symbol is " + env.sorts->sortName(ht->headsort) << endl;

  HOTerm_ptr a1 = ht->args.pop_front();
  HOTerm_ptr a2 = ht->args.pop_front();
  HOTerm_ptr a3 = ht->args.pop_front();

  if(as == B_REDUCE || as == S_REDUCE){
    a2->addArg(a3);
  }
  ht->args.push_front(a2);
  if(as == S_REDUCE){
    a3 = HSH::createHOTerm(a3);
  }
  if(as == C_REDUCE || as == S_REDUCE){
    ht->args.push_front(a3);
  }
  ht->headify(a1);
}

void CombSubstitution::addToSolved(const VarSpec& vs, HOTerm_ptr ht){
  CALL("CombSubstitution::addToSolved");

 HOTerm_ptr ht_copy = HSH::createHOTerm(ht);
  _solvedPairs.set(vs, ht_copy);
 bdAdd(new BindingBacktrackObject(this, vs)); 
}


void CombSubstitution::applyTypSub(const TypeSub* ts)
{
  CALL("CombSubstitution::applyTypSub(TypeSub*)");
 
  if(ts->isEmpty()){ return; }

  for(unsigned i = 0; i < _unificationPairs.size(); i++){
    applyTypSub(_unificationPairs[i].terml, ts);
    ASS_REP(_unificationPairs[i].terml->wellSorted(), _unificationPairs[i].terml->toStringWithTopLevelSorts());
    applyTypSub(_unificationPairs[i].termr, ts);
    ASS(_unificationPairs[i].termr->wellSorted());
  }
}

void CombSubstitution::applyTypSub(HOTerm_ptr ht, const TypeSub* ts){
  CALL("CombSubstitution::applyTypSub(HOTerm_ptr...)");   
 
  if(ht->combHead() || ht->varHead()){
    ht->headsort = applyTypSub(ht->headsort, ts);
    ht->srt = ht->sortOfLengthNPref(ht->argnum());
  }
  //need to eliminate recursive call at some point
  for(int i = ht->args.size() - 1; i >=0; i--){
    applyTypSub(ht->args[i], ts);
  } 
}

//need to update this methof
unsigned CombSubstitution::applyTypSub(unsigned sort, const TypeSub* ts){
  CALL("CombSubstitution::applyTypSub(unsigned ...)");

  if(HSH::isGround(sort)){ return sort; }  
  if(HSH::isSortVar(sort)){ return ts->apply(sort); }
  //need to eliminate recursive call at some point
  return HSH::addFuncSort(applyTypSub(HSH::domain(sort), ts), 
                          applyTypSub(HSH::range(sort), ts));
  
}

void CombSubstitution::eliminate(const VarSpec& vs, HOTerm_ptr ht)
{
  CALL("CombSubstitution::eliminate");

  for(unsigned i = 0; i < _unificationPairs.size(); i++){
    eliminate(vs, ht, _unificationPairs[i].terml);
    eliminate(vs, ht, _unificationPairs[i].termr);
  }
}

void CombSubstitution::eliminate(const VarSpec& vs, HOTerm_ptr ht, HOTerm_ptr target)
{
  CALL("CombSubstitution::eliminate");

  HOTerm_ptr targ;
  unsigned var = vs.var;
  Stack<HOTerm_ptr> toDo;
  
  toDo.push(target);
  while(!toDo.isEmpty()){
    targ = toDo.pop();
    if(targ->head.isVar() && (targ->head.var() == var)
                          && (targ->headInd == vs.index)){
      targ->headify(HSH::createHOTerm(ht));
      //If headification has resulted in a weak redex reduce it
      while(targ->combHead() && !targ->underAppliedCombTerm()){
        AlgorithmStep as = reduceStep(targ);
        switch(as){
         case I_REDUCE:
          iReduce(targ);
          break;
         case K_REDUCE:
          kReduce(targ);
          break;
         default:
          bcsReduce(targ, as);
        }
      }
    }
    for(unsigned i = 0; i < targ->argnum(); i++){
      toDo.push(targ->ntharg(i));
    }
  }
}

bool CombSubstitution::canPerformStep(AlgorithmStep ls, AlgorithmStep sls, AlgorithmStep curr){
  CALL("CombSubstitution::canPerformStep");

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


TermList CombSubstitution::apply(TermList t, int index, int sort) const
{
  CALL("CombSubstitution::apply(TermList...)");  

  ASS(sort > -1 || !t.isVar());

  Stack<HOTerm_ptr> toDo;
    
  HOTerm_ptr ht = HSH::deappify(t, index, sort);
  
  //cout << "applying to " + ht->toStringWithTopLevelSorts() << endl; 

  toDo.push(ht);

  while(!toDo.isEmpty()){
    HOTerm_ptr hterm = toDo.pop();
    if(hterm->varHead()  && hterm->headInd != UNBOUND_INDEX){
      ASS(hterm->headInd != AUX_INDEX)

      unsigned var = hterm->head.var();
      VarSpec vs(var, hterm->headInd);
      HOTerm_ptr found = deref(vs, hterm->headsort);
      ASS_REP(hterm->headsort == found->srt || hterm->isVar(), 
              hterm->toString(true, false) + " and " + found->toString(true, false) +  
                    " found of sort " + env.sorts->sortName(found->srt));
      //cout << "Dereffed " + vs.toString() + " to " + found->toString(false, true) << endl;
      hterm->headify(found);
      while(hterm->combHead() && !hterm->underAppliedCombTerm()){
        AlgorithmStep as = reduceStep(hterm);
        switch(as){
          case I_REDUCE:
            iReduce(hterm);
            break;
          case K_REDUCE:
            kReduce(hterm);
            break;
          default:
            bcsReduce(hterm, as);
        }
      }
      //cout << "The hterm post headification is " + hterm->toString(false, true) << endl;
      ASS(hterm->headInd != AUX_INDEX) 
      if(hterm->varHead()  && hterm->headInd != UNBOUND_INDEX){
        toDo.push(hterm);
        continue;
      }
    }
    for(int i = hterm->argnum() - 1; i >= 0; i--){
      toDo.push(hterm->ntharg(i));
    }
  }
  //cout << "after application" + ht->toStringWithTopLevelSorts() << endl;  
  TermList res = HSH::appify(ht);
  //cout << "returning post application " + res.toString() << endl;
  return res;
}

Literal* CombSubstitution::apply(Literal* lit, int index) const
{
  CALL("CombSubstitution::apply(Literal*...)");
  
  //Higher-order setting, no predicate symbols.
  //All literals are "= true" or "= false"
  ASS(lit->isEquality())

  if (lit->ground()) {
    return lit;
  }

  //cout << "applying to literal " + lit->toString() << endl;
  
  unsigned sort = SortHelper::getEqualityArgumentSort(lit);

  TermList arg1 = apply(*(lit->nthArgument(0)),index,sort);
  TermList arg2 = apply(*(lit->nthArgument(1)),index,sort);

  return Literal::createEquality (lit->polarity(),arg1, arg2, sort);
}

CombSubstitution::HOTerm_ptr CombSubstitution::deref(VarSpec vs, unsigned varSort) const{
  CALL("CombSubstitution::deref");
  
  //cout << "Dereffing " + vs.toString() << endl;

  HOTerm_ptr res;
  if(!_solvedPairs.find(vs, res)){
    if(!_unboundVariables.find(vs, res)){
      res = HSH::createHOTerm(TermList(_nextUnboundAvailable++, false), varSort, UNBOUND_INDEX);
      _unboundVariables.set(vs, res);
    } else {
      res = HSH::createHOTerm(res);
    }
    return res;
  }  
  
  HOTerm_ptr resCopied = HSH::createHOTerm(res);
  Stack<HOTerm_ptr> toDo;
  toDo.push(resCopied);

  while(!toDo.isEmpty()){
    HOTerm_ptr hterm = toDo.pop();
    if(hterm->varHead()){
      VarSpec vnew(hterm->head.var(), hterm->headInd);
      HOTerm_ptr found;
      if(_solvedPairs.find(vnew, found)){
        ASS(found->srt == hterm->headsort);
        found = HSH::createHOTerm(found);
        hterm->headify(found);
        toDo.push(hterm);
        continue;
      } else {
        if(!_unboundVariables.find(vnew,found)){
          found = HSH::createHOTerm(TermList(_nextUnboundAvailable++, false), hterm->headsort, UNBOUND_INDEX);
          _unboundVariables.set(vnew, found);
        } else {
          found = HSH::createHOTerm(found);
        }
        hterm->headify(found);
      }
    }
    for(int i = hterm->argnum() - 1 ; i >= 0; i--){
      toDo.push(hterm->ntharg(i));
    }
  }
  
  return resCopied;
}

/** Returns true if @b vs occurs in @b hterm, or if hterm 
  * contains an introduced arg
  */
bool CombSubstitution::occursOrNotPure(const VarSpec& vs, HOTerm_ptr hterm){
  CALL("CombSubstitution::occursOrNotPure");

  unsigned var = vs.var;
  Stack<HOTerm_ptr> toDo;
  HOTerm_ptr ht;
  
  toDo.push(hterm);
  while(!toDo.isEmpty()){
    ht = toDo.pop();
    if((ht->head.isVar() && (ht->head.var() == var) && (ht->headInd == vs.index)) ||
        isDummyArg(ht)){
      return true;
    }
    for(unsigned i = 0; i < ht->argnum(); i++){
      toDo.push(ht->ntharg(i));
    }
  }
  return false;
}

#if VDEBUG
vstring CombSubstitution::toString()
{
  CALL("CombSubstitution::toString");
  vstring res;
  SolvedType::Iterator spit(_solvedPairs);
  while(spit.hasNext()) {
    VarSpec v;
    HOTerm_ptr ht;
    spit.next(v,ht);
    res+="X"+Int::toString(v.var)+"/"+Int::toString(v.index)+ " -> ";
    res+=ht->toString(false, true)+"\n";
  }
  return res;
}
#endif

/** If terms passed to CombSubstIterator constructor are
  * unifiable by some unifier return true
  */
bool CombSubstIterator::unifiable(){
  CALL("CombSubstIterator::unifiable");

  ASS(_mode == CombSubstitution::FULL);

  while(!_unifSystem->_solved){
    //cout << _unifSystem->unificationPairsToString() << endl;
    //cout << transformStacksToString() << endl;
    while(transformStacks.top().isEmpty() && !bdStack.isEmpty()) {
      bdStack.pop().backtrack();
    }
    if(transformStacks.top().isEmpty()) {
      return false;
    }

    Transform t=transformStacks.top().pop();
    bool furtherOptions = !transformStacks.top().isEmpty();
    
    BacktrackData bd;
    bool success=transform(t,furtherOptions, bd);
    if(!success){
      bd.backtrack();
    } else {
      bdStack.push(bd);
    }
  }
  //cout << "The successful substitution is:\n " + _unifSystem->toString() << endl; 
  return true;
}

//need to comment this code AYB
bool CombSubstIterator::hasNextUnifier(){
  CALL("CombSubstIterator::hasNextUnifier");
  
  //if already solved try and find another substitution
  if(_unifSystem->_solved) {
    bdStack.pop().backtrack();
    _unifSystem->_solved=false;
  }  

  ASS(bdStack.length()+1==transformStacks.length());

  do {
    //cout << _unifSystem->unificationPairsToString() << endl;
    //cout << transformStacksToString() << endl;
    //ASSERTION_VIOLATION;
    
    while(transformStacks.top().isEmpty() && !bdStack.isEmpty()) {
      bdStack.pop().backtrack();
    }
    if(transformStacks.top().isEmpty()) {
      return false;
    }

    Transform t=transformStacks.top().pop();
    bool furtherOptions = !transformStacks.top().isEmpty();
    
    BacktrackData bd;
    bool success=transform(t,furtherOptions, bd);
    if(!success){
      bd.backtrack();
    } else {
      bdStack.push(bd);
    }
  } while(!_unifSystem->_solved);
  //cout << "The successful substitution is:\n " + _unifSystem->toString() << endl; 
  return true;
}

bool CombSubstIterator::transform(Transform t, bool furtherOptions, BacktrackData& bd){
  CALL("CombSubstIterator::transform");

  _unifSystem->bdRecord(bd);

  bool success = _unifSystem->transform(t, furtherOptions);
  if(success){
    if(!_unifSystem->_solved){
      TransformStack ts = _unifSystem->availableTransforms();
      transformStacks.backtrackablePush(ts, bd);
    }
  }
  _unifSystem->bdDone();
  return success;
}

}