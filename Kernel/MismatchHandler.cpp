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
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:{
      return isConstraintTerm(t1).isTrue() && isConstraintTerm(t2).isTrue();
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
    ASS(trm.term()->shared());
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

void MismatchHandler::introduceConstraint(TermList t1,unsigned index1, TermList t2,unsigned index2, 
  UnificationConstraintStack& ucs, BacktrackData& bd, bool recording)
{
  CALL("AtomicMismatchHandler::introduceConstraint");

  auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
  if(recording){
    ucs.backtrackablePush(constraint, bd);
  } else {
    ucs.push(constraint);
  }
}

AtomicMismatchHandler::~AtomicMismatchHandler() {}

bool MismatchHandler::handle(TermList t1, unsigned index1, TermList t2, unsigned index2, 
  UnificationConstraintStack& ucs,BacktrackData& bd, bool recording)
{
  CALL("MismatchHandler::handle");

  // make assumtion that we never create a constraint involving a variable
  // this seems reasonable
  if(t1.isOrdinaryVar() || t2.isOrdinaryVar())
    return false;

  t1 = t1.isVSpecialVar() ? TermList(get(t1.var())) : t1;
  t2 = t2.isVSpecialVar() ? TermList(get(t2.var())) : t2;

  for (auto& h : _inners) {
    if(h->isConstraintPair(t1,t2)){
      introduceConstraint(t1,index1,t2,index2,ucs,bd,recording);      
      return true;
    }
  }
  return false;
}

void MismatchHandler::addHandler(unique_ptr<AtomicMismatchHandler> hndlr){
  CALL("MismatchHandler::addHandler");
  _inners.push(std::move(hndlr));
}

MaybeBool MismatchHandler::isConstraintTerm(TermList t){
  CALL("MismatchHandler::isConstraintTerm");
  
  if(t.isVar()){ return false; }

  for (auto& h : _inners) {
    auto res = h->isConstraintTerm(t);
    if(!res.isFalse()){
      return res;
    }
  }
  return false; 
}

TermList MismatchHandler::transformSubterm(TermList trm){
  CALL("MismatchHandler::transformSubterm");

  for (auto& h : _inners) {
    TermList t = h->transformSubterm(trm);
    if(t != trm){
      return t;
    }
  }
  return trm;
}

Term* MismatchHandler::get(unsigned var)
{
  CALL("MismatchHandler::get");

  for (auto& h : _inners) {
    auto res = h->getTermMap()->tryGet(var);
    if(res.isSome()){
      return res.unwrap();
    }
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
  CALL("MismatcHandler::isConstraintTerm");
  
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
