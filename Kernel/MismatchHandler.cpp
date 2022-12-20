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

#define DEBUG(...) //DBG(__VA_ARGS__)
#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"

#include "MismatchHandler.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Kernel
{

bool UWAMismatchHandler::canAbstract(TermList t1, TermList t2) const 
{

  if(!(t1.isTerm() && t2.isTerm())) return false;
  if(t1.term()->isSort() || t2.term()->isSort()) return false;


  bool t1Interp = Shell::UnificationWithAbstractionConfig::isInterpreted(t1.term());
  bool t2Interp = Shell::UnificationWithAbstractionConfig::isInterpreted(t2.term());
  bool bothNumbers = (theory->isInterpretedConstant(t1) && theory->isInterpretedConstant(t2));

  bool okay = true;
 
  // TODO add parameter instead of reading from options
  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
  if(opt == Shell::Options::UnificationWithAbstraction::OFF){ return false; }

  switch(opt){
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
      okay &= (t1Interp && t2Interp && !bothNumbers);
      break;
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      okay &= !bothNumbers && (t1Interp || t2Interp);
      break;
    case Shell::Options::UnificationWithAbstraction::CONSTANT:
      okay &= !bothNumbers && (t1Interp || t2Interp);
      okay &= (t1Interp || env.signature->functionArity(t1.term()->functor()));
      okay &= (t2Interp || env.signature->functionArity(t2.term()->functor()));
      break; 
    case Shell::Options::UnificationWithAbstraction::ALL:
    case Shell::Options::UnificationWithAbstraction::GROUND:
      break;
    default:
      ASSERTION_VIOLATION;
  }
  return okay;

}
bool UWAMismatchHandler::tryAbstract(
      TermList o1, unsigned i1, 
      TermList o2, unsigned i2,
      RobSubstitution& subs,
      ConstraintSet& constr) const
{
  CALL("UWAMismatchHandler::checkUWA");

  auto t1 = subs.apply(o1, i1);
  auto t2 = subs.apply(o2, i2);
  auto abs = canAbstract(t1, t2);
  DEBUG("canAbstract(", t1, ",", t2, ") = ", abs);
  if (abs) {
    constr.addConstraint(o1, i1, o2, i2);
  }
  return abs;
}

// bool UWAMismatchHandler::checkUWA(TermList t1, TermList t2)
// {
// }

// bool UWAMismatchHandler::introduceConstraint(TermList t1,unsigned index1, TermList t2,unsigned index2)
// {
//   auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
//   constraints.push(constraint);
//   return true;
// }
//
// bool HOMismatchHandler::handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2)
// {
//   CALL("HOMismatchHandler::handle");
//
//   auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
//   constraints.push(constraint);
//   return true; 
// }

bool HOMismatchHandler::tryAbstract(
    TermList o1, unsigned i1, 
    TermList o2, unsigned i2,
    RobSubstitution& subs,
    ConstraintSet& constr) const
{
  // TODO
  DBG("TODO")
  return false;
}

}
