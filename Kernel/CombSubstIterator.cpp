
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

  UnifPair upair = up.unifPair;

  HSH::HOTerm hoterml = upair.first;
  HSH::HOTerm hotermr = upair.second;   

  //true here means that indices are used in the comparison
  if(hoterml.equal(hotermr, true)){
    Transform trs = make_pair(ID,BOTH);
    up.transformsLeft.push(trs);
    return;  
  }

  if(hoterml.isVar()){
    Transform trs = make_pair(ELIMINATE,FIRST);
    up.transformsLeft.push(trs);
    return;        
  }
  // if unification is between two variables arbitrarily choose to eliminate
  // left of pair
  if(hotermr.isVar() && !hoterml.isVar()){
    Transform trs = make_pair(ELIMINATE,SECOND);
    up.transformsRight.push(trs);
    return;        
  }  

  int diff = hoterml.argnum() - hotermr.argnum();
  
  if(hoterml.isAppliedVar() && diff <= 0 &&
    !hoterml.sameVarHead(hotermr,true)   &&
     hoterml.headsort == hotermr.sortOfLengthNPref(abs(diff))){
    Transform trs = make_pair(SPLIT,FIRST);
    up.transformsLeft.push(trs);       
  }

  if(hotermr.isAppliedVar()                        &&  
    (diff > 0|| (diff == 0 && !hoterml.varHead())) &&
    !hotermr.sameVarHead(hoterml,true)             &&
     hotermr.headsort == hoterml.sortOfLengthNPref(diff)){
    Transform trs = make_pair(SPLIT,SECOND);
    up.transformsRight.push(trs);       
  }

  populateSide(hoterml, FIRST, up.transformsLeft, up.lsLeft, up.lsRight);
  //If both sides have the same variable head (flex-flex) then a change on one
  //side will automatically take place on the other via eliminate
  if(!hoterml.sameVarHead(hotermr, true)){
    populateSide(hotermr, SECOND, up.transformsRight, up.lsRight, up.slsRight);
  }
  
  if(hoterml.sameFirstOrderHead(hotermr)){
    Transform trs = make_pair(DECOMP,BOTH);
    up.transformsBoth.push(trs);      
  }
  
  if(hoterml.underAppliedCombTerm() || hoterml.underAppliedCombTerm()){
    Transform trs = make_pair(ADD_ARG,BOTH);
    up.transformsBoth.push(trs); 
  }

}

void CombSubstitution::populateSide(HSH::HOTerm& hoterm, ApplyTo at, TransformStack& tStack,
                                    AlgorithmStep ls, AlgorithmStep sls){
  CALL("CombSubstitution::populateSide");
  
  if(hoterm.varHead()){
    //KX_NARROW admissable as long as var has a single argument
    if(canPerformStep(ls,sls, KX_NARROW)){
      Transform trs = make_pair(KX_NARROW,at);
      tStack.push(trs);    
    }
    
    if(hoterm.nthArgSort(0) == hoterm.sortOfLengthNPref(1)){
      if(canPerformStep(ls,sls,I_NARROW)){
        Transform trs = make_pair(I_NARROW,at);
        tStack.push(trs); 
      }      
    }
    
    if(hoterm.argnum() > 1 && (hoterm.nthArgSort(0) == hoterm.sortOfLengthNPref(2))){
      if(canPerformStep(ls, sls, K_NARROW)){
        Transform trs = make_pair(K_NARROW,at);
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
          Transform trs = make_pair(B_NARROW,at);
          tStack.push(trs);
        }        
      }
      //C narrow
      if(!(HSH::arity(sort1) < 2)){
        if((HSH::appliedToN(sort1, 2) == hoterm.sortOfLengthNPref(3)) &&
           (HSH::getNthArgSort(sort1, 0) == sort2) &&
           (HSH::getNthArgSort(sort1, 1) == sort3)){
          Transform trs = make_pair(C_NARROW,at);
          tStack.push(trs); 
        }
      }
      //S narrow
      if(!(HSH::arity(sort1) < 2) && !(HSH::arity(sort2) < 1)){
        if((HSH::appliedToN(sort1, 2) == hoterm.sortOfLengthNPref(3)) &&  
           (HSH::domain(sort1) == sort3) &&
           (HSH::domain(sort2) == sort3) &&
           (HSH::getNthArgSort(sort1, 1) == HSH::range(sort2))){
          Transform trs = make_pair(S_NARROW,at);
          tStack.push(trs);           
        }
      }
    }
    
    if(hoterm.argnum() > 1){
      unsigned sort1 = hoterm.nthArgSort(0);
      unsigned sort2 = hoterm.nthArgSort(1);
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

  if(hoterm.combHead() && !hoterm.underAppliedCombTerm()){
    AlgorithmStep as = reduceStep(hoterm);
    Transform trs = make_pair(as,at);
    tStack.push(trs);  
  }

}

CombSubstitution::AlgorithmStep CombSubstitution::reduceStep(HSH::HOTerm& ht) const
{
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
  
  //mind not working, not sure about this code
  if(t.first == ID){
    _unificationPairs.pop();
    if(_unificationPairs.isEmpty()){
      _solved = true;
    }
    return true;
  }

  //cout << "The unifcaition pairs are: " + _parent->_unifSystem->unificationPairsToString() << endl;

  BacktrackData localBD;
  bdRecord(localBD);

  bdAdd(new StackBacktrackObject(this, _unificationPairs));

  UnificationPair up = _unificationPairs.pop();
  
   cout << "carrying out transformation " + algorithmStepToString(t.first) << endl;
   cout << "on unification pair" +  up.toString() << endl;
 
  HSH::HOTerm terml = up.unifPair.first;
  HSH::HOTerm termr = up.unifPair.second;

  bool succeeded = true;
  //need to deal with indices.

  if(t.second == BOTH){
    ASS((t.first == ADD_ARG) || (t.first == DECOMP));
    
    if(t.first == ADD_ARG){
      unsigned freshArgSort = HSH::domain(terml.sort());
      HSH::HOTerm fc = HSH::HOTerm(TermList(Term::createFreshConstant("f", freshArgSort)));
      terml.addArg(fc);
      termr.addArg(fc);
      pushNewPair(terml, termr, ADD_ARG, up.lsLeft, ADD_ARG, up.lsRight);
    }

    if(t.first == DECOMP){
      ASS(terml.sameFirstOrderHead(termr));    
      HSH::HOTerm tl, tr;
      for(unsigned i = 0; i < terml.argnum(); i++){
        tl = terml.ntharg(i);
        tr = termr.ntharg(i);
        if(tl.diffFirstOrderHead(tr)){ 
          succeeded = false;
          break; 
        }
        pushNewPair(tl, tr, DECOMP, up.lsLeft, DECOMP, up.lsRight);
      }
    }
  }

  //carry out eliminate transform
  if(t.first == ELIMINATE){
    VarSpec vs;
    vs = t.second == FIRST ? VarSpec(terml.head.var(), terml.headInd) : VarSpec(termr.head.var(), termr.headInd);
    HSH::HOTerm ht = t.second == FIRST ? termr : terml;  
    if(occurs(vs, ht)){
      succeeded =  false;
    } else {
      eliminate(vs,ht);
      addToSolved(vs, ht);
    }
  }

  //split here so we can check early for failure
  if(t.first == SPLIT){
    HSH::HOTerm toSplit, other;
    toSplit = t.second == FIRST ? terml : termr; 
    other = t.second == FIRST ? termr : terml; 
    VarSpec vs(toSplit.head.var(), toSplit.headInd);
    
    HSH::HOTerm ht = HSH::HOTerm(other.head, other.headsort);
    ht.headInd = other.headInd;
    for(unsigned i = 0; i < other.argnum() - toSplit.argnum(); i ++){
      ht.addArg(other.ntharg(i));
    }
    
    if(occurs(vs, ht)){
      succeeded = false;
    } else {
      toSplit.headify(ht);
      eliminate(vs, ht, toSplit);
      eliminate(vs, ht, other);
      eliminate(vs, ht);
      addToSolved(vs, ht);
      if(t.second == FIRST){
        pushNewPair(toSplit, other, SPLIT, up.lsLeft, up.lsRight, up.slsRight);
      } else {
        pushNewPair(other, toSplit, up.lsLeft, up.slsLeft, SPLIT, up.lsRight);      
      }
    }
  }

  if(t.first != SPLIT && t.first != ELIMINATE && t.first != DECOMP && t.first != ADD_ARG){
    if(t.second == FIRST){
      transform(terml, termr, t.first);
      pushNewPair(terml, termr, t.first, up.lsLeft, up.lsRight, up.slsRight);
    } else {
      transform(termr, terml, t.first);
      pushNewPair(terml, termr, up.lsLeft, up.slsLeft, t.first, up.lsRight);
    }
  }
   
  bdDone();
  if(!succeeded) {
    localBD.backtrack();
  } else {
    bdCommit(localBD);
    localBD.drop();
  }
  if(_unificationPairs.isEmpty()){
    _solved = true;
  }
  return succeeded;

}

void CombSubstitution::transform(HSH::HOTerm& term, HSH::HOTerm& other, AlgorithmStep as){
  CALL("CombSubstitution::transform");

  if(as == I_REDUCE){
    ASS(term.headComb() == SS::I_COMB);
    iReduce(term);
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

  auto getNewVarSort = [] (AlgorithmStep as, HSH::HOTerm tm) { 
    unsigned range =  tm.sortOfLengthNPref(2);
    unsigned s1 = tm.nthArgSort(0);
    if(!(as == CX_NARROW)){ s1 = HSH::range(s1); }
    unsigned s0 = tm.nthArgSort(1);
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

  HSH::HOTerm newvar;
  unsigned oldvar = term.varHead() ? term.head.var() : 0;
  unsigned oldsort = term.headsort;
  
  if(as == I_NARROW){
    ASS(term.varHead());
    iReduce(term);
  }

  if(as == K_NARROW){
    ASS(term.varHead());
    kReduce(term);
  }

  if(as == B_NARROW || as == C_NARROW || as == S_NARROW){
    ASS(term.varHead());
    bcsReduce(term, as);
  }

  if(as == KX_NARROW){
    ASS(term.varHead());
    ASS(term.argnum() > 0);
    newvar = newVar(term.sortOfLengthNPref(1), term.headInd);
    term.args.push_front(newvar);
    kReduce(term);
  }
  
  if(as == BX_NARROW || as == CX_NARROW || as == SX_NARROW){
    ASS(term.varHead());
    ASS(term.argnum() > 1);
    newvar = newVar(getNewVarSort(as, term), term.headInd);
    term.args.push_front(newvar);    
    bcsReduce(term, getReduceEquiv(as));
  }  

  if(as >= I_NARROW && as <= SX_NARROW){
    HSH::HOTerm ht;
    VarSpec vs = VarSpec(oldvar, term.headInd);
    if(as == KX_NARROW || as == BX_NARROW || 
       as == CX_NARROW || as == SX_NARROW){
      unsigned combSort = HSH::addFuncSort(newvar.sort(), oldsort);      
      ht = HSH::HOTerm(HSH::getCombTerm(convert(as), combSort));
      ht.addArg(newvar);
    } else {
      ht = HSH::HOTerm(HSH::getCombTerm(convert(as), oldsort));
    }
    eliminate(vs, ht, term);
    eliminate(vs, ht, other);
    eliminate(vs, ht);
    addToSolved(vs, ht);
  }

}

void CombSubstitution::iReduce(HSH::HOTerm& ht) const{ 
  CALL("CombSubstitution::iReduce");

  HSH::HOTerm a1 = ht.args.pop_front();
  ht.headify(a1);
}

void CombSubstitution::kReduce(HSH::HOTerm& ht) const{
  CALL("CombSubstitution::kReduce");

  HSH::HOTerm a1 = ht.args.pop_front();
  ht.args.pop_front();
  ht.headify(a1);
}

void CombSubstitution::bcsReduce(HSH::HOTerm& ht, AlgorithmStep as) const{
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

void CombSubstitution::pushNewPair(HSH::HOTerm& ht1, HSH::HOTerm& ht2,
     AlgorithmStep lsl, AlgorithmStep slsl, AlgorithmStep lsr, AlgorithmStep slsr ){
  CALL("CombSubstitution::pushNewPair");
  
  UnificationPair newup = UnificationPair(ht1, ht2, lsl, slsl, lsr, slsr);
  populateTransformations(newup);
  _unificationPairs.push(newup);                                       
}

void CombSubstitution::eliminate(VarSpec vs, HSH::HOTerm ht)
{
  CALL("CombSubstitution::eliminate");

  for(unsigned i = 0; i < _unificationPairs.size(); i++){
    eliminate(vs, ht, _unificationPairs[i].unifPair.first);
    eliminate(vs, ht, _unificationPairs[i].unifPair.second);
  }
}

void CombSubstitution::eliminate(VarSpec vs, HSH::HOTerm ht, HSH::HOTerm& target)
{
  CALL("CombSubstitution::eliminate");

  HSH::HOTerm* targ = &target;
  unsigned var = vs.var;
  Stack<HSH::HOTerm*> toDo;

  toDo.push(targ);
  while(!toDo.isEmpty()){
    targ = toDo.pop();
    if(targ->head.isVar() && (targ->head.var() == var)
                          && (targ->headInd == vs.index)){
      targ->headify(ht);
      //If headification has resulted in a weak redex reduce it
      while(targ->combHead() && !targ->underAppliedCombTerm()){
        AlgorithmStep as = reduceStep(*targ);
        switch(as){
         case I_REDUCE:
          iReduce(*targ);
          break;
         case K_REDUCE:
          kReduce(*targ);
          break;
         default:
          bcsReduce(*targ, as);
        }
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


TermList CombSubstitution::apply(TermList t, int index) const
{
  CALL("CombSubstitution::apply(TermList...)");  

  Stack<HSH::HOTerm*> toDo;
  DHMap<VarSpec, HSH::HOTerm, VarSpec::Hash1, VarSpec::Hash2> known;
  
  HSH::HOTerm ht = HSH::deappify(t, index);
   
  toDo.push(&ht);

  while(!toDo.isEmpty()){
    HSH::HOTerm* hterm = toDo.pop();
    if(hterm->varHead() && hterm->head.var() <= _maxOrigVar){
      unsigned var = hterm->head.var();
      VarSpec vs(var, hterm->headInd);
      HSH::HOTerm found;
      bool success = false;
      if(known.find(vs, found)){
        success = true;
      } else {
        found = deref(vs, success);
        if(success){
          known.insert(vs, found);
        }
      }
      if(success){
        hterm->headify(found);
        while(hterm->combHead() && !hterm->underAppliedCombTerm()){
          AlgorithmStep as = reduceStep(*hterm);
          switch(as){
            case I_REDUCE:
              iReduce(*hterm);
              break;
            case K_REDUCE:
              kReduce(*hterm);
              break;
            default:
              bcsReduce(*hterm, as);
          }
        }
        toDo.push(hterm);
        continue;         
      }
    }
    for(unsigned i = 0; i < hterm->argnum(); i++){
      toDo.push(hterm->nthargptr(i));
    }
  }
  TermList res = HSH::appify(ht);
  return res;
}

Literal* CombSubstitution::apply(Literal* lit, int index) const
{
  CALL("CombSubstitution::apply(Literal*...)");
  static DArray<TermList> ts(32);

  if (lit->ground()) {
    return lit;
  }

  int arity = lit->arity();
  ts.ensure(arity);
  int i = 0;
  for (TermList* args = lit->args(); ! args->isEmpty(); args = args->next()) {
    ts[i++]=apply(*args,index);
  }
  return Literal::create(lit,ts.array());
}

HOSortHelper::HOTerm CombSubstitution::deref(VarSpec vs, bool& success) const{
  CALL("CombSubstitution::deref");
  
  HSH::HOTerm res;
  if(!_solvedPairs.find(vs, res)){
    success = false;
    return res;
  }  
  
  success = true;
  Stack<HSH::HOTerm*> toDo;
  toDo.push(&res);
  
  while(!toDo.isEmpty()){
    HSH::HOTerm* hterm = toDo.pop();
    if(hterm->varHead()){
      VarSpec vnew(hterm->head.var(), hterm->headInd);
      HSH::HOTerm found;
      if(_solvedPairs.find(vnew, found)){
        hterm->headify(found);
      }
    }
    for(unsigned i = 0; i < hterm->argnum(); i++){
      toDo.push(hterm->nthargptr(i));
    }
  }
  return res;
}

bool CombSubstitution::occurs(VarSpec vs, const HSH::HOTerm& hterm){
  CALL("CombSubstitution::occurs");

  unsigned var = vs.var;
  Stack<HSH::HOTerm> toDo;
  HSH::HOTerm ht;
  
  toDo.push(hterm);
  while(!toDo.isEmpty()){
    ht = toDo.pop();
    if(ht.head.isVar() && (ht.head.var() == var)
                       && (ht.headInd == vs.index)){
      return true;
    }
    for(unsigned i = 0; i < ht.argnum(); i++){
      toDo.push(ht.ntharg(i));
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
    HSH::HOTerm ht;
    spit.next(v,ht);
    res+="X"+Int::toString(v.var)+"/"+Int::toString(v.index)+ " -> ";
    res+=ht.toString(false, true)+"\n";
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

    while(transformStacks.top().isEmpty() && !bdStack.isEmpty()) {
      bdStack.pop().backtrack();
    }
    if(transformStacks.top().isEmpty()) {
      return false;
    }
    
    Transform t=transformStacks.top().pop();
    
    BacktrackData bd;
    bool success=transform(t,bd);
    if(!success){
      bd.backtrack();
    } else {
      bdStack.push(bd);
    }
  } while(!_unifSystem->_solved);
  cout << "The successful substitution is:\n " + _unifSystem->toString() << endl; 
  return true;
}

bool CombSubstIterator::transform(Transform t, BacktrackData& bd){
  CALL("CombSubstIterator::transform");

  _unifSystem->bdRecord(bd);

  bool success = _unifSystem->transform(t);
  if(success){
    if(!_unifSystem->_solved){
      TransformStack ti = _unifSystem->availableTransforms();
      transformStacks.backtrackablePush(ti, bd);
    }
  }
  _unifSystem->bdDone();
  return success;
}

}