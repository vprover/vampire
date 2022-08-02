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
 * @file MismatchHandler.cpp
 * Defines class MismatchHandler.
 *
 */

#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"
#include "Lib/BiMap.hpp"

#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "SortHelper.hpp"

#include "MismatchHandler.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Kernel
{

bool UWAMismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
  UnificationConstraintStack& ucs,BacktrackData& bd, bool recording)
{
  CALL("UWAMismatchHandler::handle");

  if(t1.isOrdinaryVar() || t2.isOrdinaryVar()) return false;

  Term* tm1 = 0;
  Term* tm2 = 0;
  if(t1.isVSpecialVar() && !_termMap.find(t1.var(), tm1)) return false;
  if(t2.isVSpecialVar() && !_termMap.find(t2.var(), tm2)) return false;

  if(!tm1) tm1 = t1.term();
  if(!tm2) tm2 = t2.term();
  
  if(checkUWA(TermList(tm1),TermList(tm2))){
    if(areIdentical(tm1,tm2,index1,index2))
      return true;

    return introduceConstraint(TermList(tm1),index1,TermList(tm2),index2,ucs,bd,recording);
  }
  return false;
}

bool UWAMismatchHandler::checkUWA(TermList t1, TermList t2)
{
  CALL("UWAMismatchHandler::checkUWA");

  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();

  switch(opt){
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      return isConstraintTerm(t1).isTrue() || isConstraintTerm(t2).isTrue();
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:{
      bool b = isConstraintTerm(t1).isTrue() && isConstraintTerm(t2).isTrue();
      return b;
    }
    default:
      // handler should never be called if UWA is off
      ASSERTION_VIOLATION;
      return false;
  }
}

TermList UWAMismatchHandler::transformSubterm(TermList trm)
{
  CALL("UWAMismatchHandler::transformSubterm");
 
  if(isConstraintTerm(trm).isTrue()){
    return TermList::getVSpecVar(trm.term(), &_termMap);
  }
  return trm;
}

MaybeBool UWAMismatchHandler::isConstraintTerm(TermList t){
  CALL("UWAMismatchHandler::isConstraintTerm");
  
  if(t.isVar()){ return false; }

  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
  bool onlyInterpreted = opt == Shell::Options::UnificationWithAbstraction::INTERP_ONLY;

  auto trm = t.term();
  bool isNumeral = Shell::UnificationWithAbstractionConfig::isNumeral(t);

  if(Shell::UnificationWithAbstractionConfig::isInterpreted(trm) && !isNumeral){
    return true;    
  }

  TermList sort = SortHelper::getResultSort(t.term()); 
  if(!onlyInterpreted && (sort.isVar() || sort.isIntSort() || sort.isRatSort() || sort.isRealSort())){
    return MaybeBool::UNKNOWN;
  }  

  return false;
}

#if VDEBUG
  Term* UWAMismatchHandler::get(unsigned var)
  {
    CALL("UWAMismatchHandler::get");
     
    auto res = _termMap.tryGet(var);
    ASS(res.isSome());
    return res.unwrap();
  }
#endif

bool MismatchHandler::introduceConstraint(TermList t1,unsigned index1, TermList t2,unsigned index2, 
  UnificationConstraintStack& ucs, BacktrackData& bd, bool recording)
{
  CALL("MismatchHandler::introduceConstraint");

  auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
  if(recording){
    ucs.backtrackablePush(constraint, bd);
  } else {
    ucs.push(constraint);
  }
  return true;
}

bool MismatchHandler::areIdentical(Term* t1, Term* t2, unsigned idx1, unsigned idx2)
{
  CALL("MismatchHandler::areIdentical");

  if(t1 == t2 && t1->shared() && t1->ground()){ return true; }
 
  TermList tt1 = TermList(t1);
  TermList tt2 = TermList(t2);

  RobSubstitution::TermSpec t1spec = RobSubstitution::TermSpec(tt1, idx1);
  RobSubstitution::TermSpec t2spec = RobSubstitution::TermSpec(tt2, idx2);
  if(t1spec.sameTermContent(t2spec)){ return true; }

  return false;
}


CompositeMismatchHandler::~CompositeMismatchHandler(){
  MHList::destroyWithDeletion(_inners);
}

bool CompositeMismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
  UnificationConstraintStack& ucs,BacktrackData& bd, bool recording)
{
  CALL("CompositeMismatchHandler::handle");

  MHList* hit=_inners;
  while(hit) {
    if(hit->head()->handle(t1,index1,t2,index2,ucs,bd,recording)){
      return true;
    }
    hit=hit->tail();
  }
  return false;
}

void CompositeMismatchHandler::addHandler(MismatchHandler* hndlr){
  CALL("CompositeMismatchHandler::addHandler");

  MHList::push(hndlr,_inners);
}

MaybeBool CompositeMismatchHandler::isConstraintTerm(TermList t){
  CALL("CompositeMismatchHandler::isConstraintTerm");
  
  if(t.isVar()){ return false; }

  MHList* hit=_inners;
  while(hit) {
    auto res = hit->head()->isConstraintTerm(t);
    if(!res.isFalse()){
      return res;
    }
    hit=hit->tail();
  }
  return false; 
}

TermList CompositeMismatchHandler::transformSubterm(TermList trm){
  CALL("CompositeMismatchHandler::transformSubterm");

  MHList* hit=_inners;
  while(hit) {
    TermList t = hit->head()->transformSubterm(trm);
    if(t != trm){
      return t;
    }
    hit=hit->tail();
  }
  return trm;
}

Term* CompositeMismatchHandler::get(unsigned var)
{
  CALL("CompositeMismatchHandler::get");

  MHList* hit=_inners;
  while(hit) {
    auto res = hit->head()->getTermMap()->tryGet(var);
    if(res.isSome()){
      return res.unwrap();
    }
    hit=hit->tail();
  } 
  ASSERTION_VIOLATION;
}


bool HOMismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2,
  UnificationConstraintStack& ucs, BacktrackData& bd, bool recording)
{
  CALL("HOMismatchHandler::handle");

  if(t1.isOrdinaryVar() || t2.isOrdinaryVar()) return false;

  Term* tm1 = 0;
  Term* tm2 = 0;
  if(t1.isVSpecialVar() && !_termMap.find(t1.var(), tm1)) return false;
  if(t2.isVSpecialVar() && !_termMap.find(t2.var(), tm2)) return false;

  if(!tm1) tm1 = t1.term();
  if(!tm2) tm2 = t2.term();

  if(isConstraintTerm(TermList(tm1)).isFalse() || isConstraintTerm(TermList(tm2)).isFalse())
    return false;
  
  if(areIdentical(tm1,tm2,index1,index2))
    return true;

  return introduceConstraint(TermList(tm1),index1,TermList(tm2),index2,ucs,bd,recording);
}

MaybeBool HOMismatchHandler::isConstraintTerm(TermList t){
  CALL("CompositeMismatcHandler::isConstraintTerm");
  
  //TODO Bool sort???
  if(t.isVar()){ return false; }

  auto trm = t.term();
  auto sort = SortHelper::getResultSort(trm);
  
  if(sort.isArrowSort()){
    return true;
  }

  if(sort.isVar()){
    return MaybeBool::UNKNOWN;
  }
  return false;
}

TermList HOMismatchHandler::transformSubterm(TermList trm)
{
  CALL("HOMismatchHandler::transformSubterm");

  // isConstraintTerm or Bool?  
  //TODO
  ASSERTION_VIOLATION;
}


}
