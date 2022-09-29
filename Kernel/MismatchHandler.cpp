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

bool UWAMismatchHandler::isConstraintPair(TermList t1, TermList t2)
{
  CALL("UWAMismatchHandler::isConstraintPair");

  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();

  switch(opt){
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      return isConstraintTerm(t1).isTrue() || isConstraintTerm(t2).isTrue();
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
      return isConstraintTerm(t1).isTrue() && isConstraintTerm(t2).isTrue();
    case Shell::Options::UnificationWithAbstraction::ONE_SIDE_NL:
      return (isConstraintTerm(t1).isTrue() && isConstraintTerm(t2).maybe()) ||
             (isConstraintTerm(t2).isTrue() && isConstraintTerm(t1).maybe()) ||
             (isConstraintTerm(t2).isTrue() && isConstraintTerm(t1).isTrue());
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
    ASS(trm.term()->shared());
    return TermList::getVSpecVar(trm.term(), &_termMap);
  }
  return trm;
}

MaybeBool UWAMismatchHandler::isConstraintTerm(TermList t){
  CALL("UWAMismatchHandler::isConstraintTerm");
  
  if(t.isVar()){ return false; }

  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();

  auto trm = t.term();
  bool isNumeral = Shell::UnificationWithAbstractionConfig::isNumeral(t);

  if(Shell::UnificationWithAbstractionConfig::isInterpreted(trm) && !isNumeral){
    return true;    
  }

  TermList sort = SortHelper::getResultSort(trm); 
  switch(opt){
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      if(sort.isVar() || sort.isIntSort() || sort.isRatSort() || sort.isRealSort()){
        return MaybeBool::UNKNOWN;
      }
      return false;      
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
      return false;
    case Shell::Options::UnificationWithAbstraction::ONE_SIDE_NL:
      if(env.signature->getFunction(trm->functor())->finalLoopCount()){
        return MaybeBool::UNKNOWN;        
      }
      return false;
    default:
      // handler should never be called if UWA is off
      ASSERTION_VIOLATION;
      return false;
  }
}

void MismatchHandler::introduceConstraint(TermList t1,unsigned index1, TermList t2,unsigned index2, 
  UnificationConstraintStack& ucs, BacktrackData& bd, bool recording)
{
  CALL("MismatchHandler::introduceConstraint");

  auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
  if(recording){
    ucs.backtrackablePush(constraint, bd);
  } else {
    ucs.push(constraint);
  }
}

CompositeMismatchHandler::~CompositeMismatchHandler(){
  CALL("CompositeMismatchHandler::~CompositeMismatchHandler");

  MHList::destroyWithDeletion(_inners);
}

bool CompositeMismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
  UnificationConstraintStack& ucs,BacktrackData& bd, bool recording)
{
  CALL("CompositeMismatchHandler::handle");

  // make assumtion that we never create a constraint involving a variable
  // this seems reasonable
  if(t1.isOrdinaryVar() || t2.isOrdinaryVar())
    return false;

  t1 = t1.isVSpecialVar() ? TermList(get(t1.var())) : t1;
  t2 = t2.isVSpecialVar() ? TermList(get(t2.var())) : t2;

  MHList* hit=_inners;
  while(hit) {
    if(hit->head()->isConstraintPair(t1,t2)){
      introduceConstraint(t1,index1,t2,index2,ucs,bd,recording);      
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


bool HOMismatchHandler::isConstraintPair(TermList t1, TermList t2)
{
  CALL("HOMismatchHandler::isConstraintPair");

  auto isBooleanOrConstraintTerm = [&](TermList t){
    TermList sort = SortHelper::getResultSort(t.term());
    return !isConstraintTerm(t).isFalse() || sort.isBoolSort();
  };

  return isBooleanOrConstraintTerm(t1) && isBooleanOrConstraintTerm(t2);
}

MaybeBool HOMismatchHandler::isConstraintTerm(TermList t){
  CALL("CompositeMismatcHandler::isConstraintTerm");
  
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

  if(trm.isVar()) return trm;

  ASS(trm.term()->shared());

  TermList sort = SortHelper::getResultSort(trm.term());
  if(sort.isBoolSort()){
    return TermList::getVSpecVar(trm.term(), &_termMap);    
  }

  if(!isConstraintTerm(trm).isFalse()){
    return TermList::getVSpecVar(trm.term(), &_termMap);
  }
  return trm;
}


}
