
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
 * Implements polynomial modification of the Robinson unification algorithm.
 */

#include "Lib/Environment.hpp"

#include "Lib/Hash.hpp"
#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Int.hpp"

#include "SortHelper.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"
#include "Signature.hpp"
#include "HOSortHelper.hpp"

#include "Indexing/TermSharing.hpp"

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

  populateTransformations(_unificationPairs.top());

  UnificationPair up = _unificationPairs.top();

  TransformStack left = up.transformsLeft;
  TransformStack right = up.transformsRight;
  TransformStack both = up.transformsBoth;
 
  if(!both.isEmpty()){
    return both;
  } else {
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

  //cout << "terml is " + hoterml->toString(false, true) << endl;
  //cout << "termr is " + hotermr->toString(false, true) << endl;
  
  //true here means that indices are used in the comparison
  if(HSH::equal(hotermr, hoterml, true)){
    Transform trs = make_pair(ID,BOTH);
    up.transformsLeft.push(trs);
    return;  
  }

  if(hoterml->isVar()){
    Transform trs = make_pair(ELIMINATE,FIRST);
    up.transformsLeft.push(trs);
    return;        
  }
  
  // if unification is between two variables arbitrarily choose to eliminate
  // left of pair
  if(hotermr->isVar() && !hoterml->isVar()){
    Transform trs = make_pair(ELIMINATE,SECOND);
    up.transformsRight.push(trs);
    return;        
  }  

  if(hoterml->sameFirstOrderHead(hotermr)){
    Transform trs = make_pair(DECOMP,BOTH);
    up.transformsBoth.push(trs);
    return;      
  }
  
  if(hoterml->underAppliedCombTerm() || hoterml->underAppliedCombTerm()){
    Transform trs = make_pair(ADD_ARG,BOTH);
    up.transformsBoth.push(trs);
    return; 
  }

  if(hoterml->combHead() && !hoterml->underAppliedCombTerm()){
    AlgorithmStep as = reduceStep(hoterml);
    Transform trs = make_pair(as,FIRST);
    up.transformsLeft.push(trs);
    return;  
  } else if(hotermr->combHead() && !hotermr->underAppliedCombTerm()){
    AlgorithmStep as = reduceStep(hotermr);
    Transform trs = make_pair(as,SECOND);
    up.transformsRight.push(trs);
    return;
  }

  int diff = hoterml->argnum() - hotermr->argnum();
  
  if(hoterml->isAppliedVar() && diff <= 0 &&
    !hoterml->sameVarHead(hotermr,true)   &&
     hoterml->headsort == hotermr->sortOfLengthNPref(abs(diff))){
    Transform trs = make_pair(SPLIT,FIRST);
    up.transformsLeft.push(trs);       
  }

  if(hotermr->isAppliedVar()                        &&  
    (diff > 0|| (diff == 0 && !hoterml->varHead())) &&
    !hotermr->sameVarHead(hoterml,true)             &&
     hotermr->headsort == hoterml->sortOfLengthNPref(diff)){
    Transform trs = make_pair(SPLIT,SECOND);
    up.transformsRight.push(trs);       
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
    Transform trs = make_pair(KX_NARROW,at);
    tStack.push(trs);    
  }
  
  if(hoterm->nthArgSort(0) == hoterm->sortOfLengthNPref(1)){
    if(canPerformStep(ls,sls,I_NARROW)){
      Transform trs = make_pair(I_NARROW,at);
      tStack.push(trs); 
    }      
  }
  
  if(hoterm->argnum() > 1 && (hoterm->nthArgSort(0) == hoterm->sortOfLengthNPref(2))){
    if(canPerformStep(ls, sls, K_NARROW)){
      Transform trs = make_pair(K_NARROW,at);
      tStack.push(trs);
    }       
  }

  if(hoterm->argnum() > 2){
    cout << hoterm->toStringWithTopLevelSorts() << endl;
    unsigned sort1 = hoterm->nthArgSort(0);
    unsigned sort2 = hoterm->nthArgSort(1);
    unsigned sort3 = hoterm->nthArgSort(2);
    //B narrow  
    if(!(HSH::arity(sort1) < 1) && !(HSH::arity(sort2) < 1)){
      if((HSH::domain(sort1) == HSH::range(sort2) &&
         (HSH::domain(sort2) == sort3) &&
         (HSH::range(sort1) == hoterm->sortOfLengthNPref(3)))){
        Transform trs = make_pair(B_NARROW,at);
        tStack.push(trs);
      }        
    }
    //C narrow
    if(!(HSH::arity(sort1) < 2)){
      if((HSH::appliedToN(sort1, 2) == hoterm->sortOfLengthNPref(3)) &&
         (HSH::getNthArgSort(sort1, 0) == sort2) &&
         (HSH::getNthArgSort(sort1, 1) == sort3)){
        Transform trs = make_pair(C_NARROW,at);
        tStack.push(trs); 
      }
    }
    //S narrow
    if(!(HSH::arity(sort1) < 2) && !(HSH::arity(sort2) < 1)){
      if((HSH::appliedToN(sort1, 2) == hoterm->sortOfLengthNPref(3)) &&  
         (HSH::domain(sort1) == sort3) &&
         (HSH::domain(sort2) == sort3) &&
         (HSH::getNthArgSort(sort1, 1) == HSH::range(sort2))){
        Transform trs = make_pair(S_NARROW,at);
        tStack.push(trs);           
      }
    }
  }
  
  if(hoterm->argnum() > 1){
    unsigned sort1 = hoterm->nthArgSort(0);
    unsigned sort2 = hoterm->nthArgSort(1);
    if(!(HSH::arity(sort1) < 1)){
      if(HSH::domain(sort1) == sort2){
        Transform trs = make_pair(BX_NARROW,at);
        tStack.push(trs);
        Transform trs2 = make_pair(SX_NARROW,at);
        tStack.push(trs2);
      }
    }
    if(canPerformStep(ls, sls, CX_NARROW)){
      Transform trs = make_pair(CX_NARROW,at);
      tStack.push(trs);
    }          
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

bool CombSubstitution::transform(Transform t, bool furtherOptions){
  CALL("CombSubstitution::transform");
  
  BacktrackData localBD;
  bdRecord(localBD);

  //Only want to record existing unification pairs if there is the possibility of 
  //backtracking to them. If from existing system, no the current transform is the only
  //available transform, then there is no point in recording the pairs.
  if(furtherOptions){
    bdAdd(new StackBacktrackObject(this, _unificationPairs));
  }

  UnificationPair* up = &_unificationPairs.top();
  //temporary measure, in the long run, manipulate transforms rather than emptying them.
  up->emptyTransforms();

  cout << "carrying out transformation " + algorithmStepToString(t.first) << endl;
  cout << "on unification pair" +  up->toString() << endl;
  //cout << "The substitution so far is " + toString() << endl; 
 
  HOTerm_ptr terml = up->terml;
  HOTerm_ptr termr = up->termr;

  bool succeeded = true;
  //need to deal with indices.

  if(t.first == ID){
    _unificationPairs.pop();
  }
  
  if(t.second == BOTH && t.first != ID){
    ASS((t.first == ADD_ARG) || (t.first == DECOMP));
    
    if(t.first == ADD_ARG){
      unsigned freshArgSort = HSH::domain(terml->sort());
      TermList newArg = TermList(Term::createFreshConstant("f",freshArgSort, true));
      HOTerm_ptr fcl = HOTerm_ptr(new HSH::HOTerm(newArg));
      HOTerm_ptr fcr = HOTerm_ptr(new HSH::HOTerm(newArg));
      terml->addArg(fcl);
      termr->addArg(fcr);
      up->lsRight = UNDEFINED;
      up->lsLeft = UNDEFINED;
      up->slsRight = UNDEFINED;
      up->slsLeft = UNDEFINED;
    }

    if(t.first == DECOMP){
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
  if(t.first == ELIMINATE){
    VarSpec vs;
    vs = t.second == FIRST ? VarSpec(terml->head.var(), terml->headInd) 
                           : VarSpec(termr->head.var(), termr->headInd);
    HOTerm_ptr ht = t.second == FIRST ? termr : terml; 
    if(occursOrNotPure(vs, ht)){
      succeeded =  false;
    } else {
      eliminate(vs, ht);
      addToSolved(vs, ht);
      _unificationPairs.pop();
    }
  }

  //split here so we can check early for failure
  if(t.first == SPLIT){
    HOTerm_ptr toSplit;
    HOTerm_ptr other;
    toSplit = t.second == FIRST ? terml : termr; 
    other = t.second == FIRST ? termr : terml; 
    VarSpec vs(toSplit->head.var(), toSplit->headInd);
    
    HOTerm_ptr ht = HOTerm_ptr(new HSH::HOTerm(other->head, other->headsort));
    ht->headInd = other->headInd;
    for(unsigned i = 0; i < other->argnum() - toSplit->argnum(); i ++){
      ht->addArg(other->ntharg(i));
    }
    
    if(occursOrNotPure(vs, ht)){
      succeeded = false;
    } else {
      toSplit->headify(ht);
      eliminate(vs, ht, toSplit);
      eliminate(vs, ht, other);
      eliminate(vs, ht);
      addToSolved(vs, ht);
      if(t.second == FIRST){
        //have made left head same as right, so make last steps on left side same as those on right
        up->lsLeft = up->lsRight;
        up->slsLeft = up->slsRight;
      } else {
        up->lsRight = up->lsLeft;
        up->slsRight = up->slsLeft;      
      }
    }
  }

  if(t.first != SPLIT && t.first != ELIMINATE && t.first != DECOMP && t.first != ADD_ARG){
    if(t.second == FIRST){
      transform(terml, termr, t.first);
      up->slsLeft = up->lsLeft;
      up->lsLeft = t.first;
    } else {
      transform(termr, terml, t.first);
      up->slsRight = up->lsRight;
      up->lsRight = t.first;
    }
    up->mostRecentSide = t.second;
  }
   
  //cout << "at this point the substitution is " + toString() << endl;

  bdDone();
  if(!succeeded) {
    localBD.backtrack();
  } else {
    bdCommit(localBD);
    localBD.drop();
  }
  if(_unificationPairs.isEmpty() && succeeded){
    _solved = true;
  }
  return succeeded;

}

void CombSubstitution::transform(HOTerm_ptr term, HOTerm_ptr other, AlgorithmStep as){
  CALL("CombSubstitution::transform");

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

  auto getNewVarSort = [] (AlgorithmStep as, HOTerm_ptr tm) { 
    unsigned range =  tm->sortOfLengthNPref(2);
    unsigned s1 = tm->nthArgSort(0);
    if(!(as == CX_NARROW)){ s1 = HSH::range(s1); }
    unsigned s0 = tm->nthArgSort(1);
    unsigned newVarSort = env.sorts->addFunctionSort(s1, range);
    if(!(as == BX_NARROW)){
      newVarSort = HSH::addFuncSort(s0, newVarSort);
    }
    return newVarSort;
  };

  auto getReduceEquiv =[](AlgorithmStep as){
    switch(as){
      case BX_NARROW:
        return B_REDUCE;
      case CX_NARROW:
        return C_REDUCE;
      case SX_NARROW:
        return S_REDUCE;
      default:
        ASSERTION_VIOLATION;
    }
  };

  HOTerm_ptr newvar;
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
    bcsReduce(term, as);
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
    newvar = newVar(getNewVarSort(as, term), term->headInd);
    term->args.push_front(newvar);    
    bcsReduce(term, getReduceEquiv(as));
  }  

  if(as >= I_NARROW && as <= SX_NARROW){
    HOTerm_ptr ht;
    VarSpec vs = VarSpec(oldvar, oldInd);
    if(as == KX_NARROW || as == BX_NARROW || 
       as == CX_NARROW || as == SX_NARROW){
      unsigned combSort = HSH::addFuncSort(newvar->sort(), oldsort);      
      ht = HOTerm_ptr(new HSH::HOTerm(HSH::getCombTerm(convert(as), combSort)));
      ht->addArg(newvar);
    } else {
      ht = HOTerm_ptr(new HSH::HOTerm(HSH::getCombTerm(convert(as), oldsort)));
    }
    eliminate(vs, ht, term);
    eliminate(vs, ht, other);
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
  //cout << "The sort of arg1 is " + env.sorts->sortName(a1->srt) << endl;
  HOTerm_ptr a2 = ht->args.pop_front();
  //cout << "The sort of arg2 is " + env.sorts->sortName(a2->srt) << endl;
  HOTerm_ptr a3 = ht->args.pop_front();
  //cout << "The sort of arg3 is " + env.sorts->sortName(a3->srt) << endl;

  if(as == B_REDUCE || as == S_REDUCE){
    a2->addArg(a3);
  }
  ht->args.push_front(a2);
  if(as == S_REDUCE){
    a3 = HOTerm_ptr(new HSH::HOTerm(*a3));
  }
  if(as == C_REDUCE || as == S_REDUCE){
    ht->args.push_front(a3);
  }
  ht->headify(a1);
}

void CombSubstitution::addToSolved(const VarSpec& vs, HOTerm_ptr ht){
  CALL("CombSubstitution::addToSolved");
 
 HOTerm_ptr ht_copy = HOTerm_ptr(new HSH::HOTerm(*ht));
  _solvedPairs.set(vs, ht_copy);
 bdAdd(new BindingBacktrackObject(this, vs)); 
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
      targ->headify(ht);
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
  DHMap<VarSpec, HOTerm_ptr, VarSpec::Hash1, VarSpec::Hash2> known;
    
  HOTerm_ptr ht = HSH::deappify(t, index, sort);
  
 // cout << "applying to " + ht->toString(false, true) + " of sort " + (sort > -1 ?
   //       env.sorts->sortName(sort) : "") << endl; 
  
  toDo.push(ht);

  while(!toDo.isEmpty()){
    HOTerm_ptr hterm = toDo.pop();
    if(hterm->varHead()  && hterm->headInd != UNBOUND_INDEX){
      ASS(hterm->headInd != AUX_INDEX)

      unsigned var = hterm->head.var();
      VarSpec vs(var, hterm->headInd);
      HOTerm_ptr found;
      if(!known.find(vs, found)){
        bool present = false;
        found = deref(vs, present, hterm->headsort);
        if(present){
          known.insert(vs, found);
        }
      }
      ASS_REP(hterm->headsort == found->srt || hterm->isVar(), 
              hterm->toString(true, false) + " and " + found->toString(true, false) +  
                    " found of sort " + env.sorts->sortName(found->srt));
      //cout << "Dereffed " + vs.toString() + " to " + found.toString(false, true) << endl;
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

CombSubstitution::HOTerm_ptr CombSubstitution::deref(VarSpec vs, bool& success, unsigned varSort) const{
  CALL("CombSubstitution::deref");
  
  //cout << "Dereffing " + vs.toString() << endl;

  HOTerm_ptr res;
  if(!_solvedPairs.find(vs, res)){
    if(!_unboundVariables.find(vs, res)){
      res = HOTerm_ptr(new HSH::HOTerm(TermList(_nextUnboundAvailable++, false), varSort, UNBOUND_INDEX));
      _unboundVariables.set(vs, res);
    } else {
      res = HOTerm_ptr(new HSH::HOTerm(*res));
    }
    return res;
  }  
  
  HOTerm_ptr resCopied = HOTerm_ptr(new HSH::HOTerm(*res));
  success = true;
  Stack<HOTerm_ptr> toDo;
  toDo.push(resCopied);

  while(!toDo.isEmpty()){
    HOTerm_ptr hterm = toDo.pop();
    if(hterm->varHead()){
      VarSpec vnew(hterm->head.var(), hterm->headInd);
      HOTerm_ptr found;
      if(_solvedPairs.find(vnew, found)){
        ASS(found->srt == hterm->headsort);
        found = HOTerm_ptr(new HSH::HOTerm(*found));
        hterm->headify(found);
        //cout << "FROM DEREF found is " + found->toString(true, false) << endl; 
        //cout << "FROM DEREF, after headification " + hterm->toString(false, true) << endl;
        toDo.push(hterm);
        continue;
      } else {
        if(!_unboundVariables.find(vnew,found)){
          found = HOTerm_ptr(new HSH::HOTerm(TermList(_nextUnboundAvailable++, false), hterm->headsort, UNBOUND_INDEX));
          _unboundVariables.set(vnew, found);
        } else {
          found = HOTerm_ptr(new HSH::HOTerm(*found));
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
    cout << _unifSystem->unificationPairsToString() << endl;
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
  cout << "The successful substitution is:\n " + _unifSystem->toString() << endl; 
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