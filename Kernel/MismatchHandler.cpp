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


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"

#include "MismatchHandler.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

namespace Kernel
{

bool UWAMismatchHandler::handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2)
{
  CALL("UWAMismatchHandler::handle");

    TermList tt1 = sub->apply(t1,index1);
    TermList tt2 = sub->apply(t2,index2);

  if(checkUWA(tt1,tt2)){
    return introduceConstraint(t1,index1,t2,index2);
  }
  return false;
}

bool UWAMismatchHandler::checkUWA(TermList t1, TermList t2)
{
  CALL("UWAMismatchHandler::checkUWA");

    if(!(t1.isTerm() && t2.isTerm())) return false;

    bool t1Interp = Shell::UnificationWithAbstractionConfig::isInterpreted(t1.term());
    bool t2Interp = Shell::UnificationWithAbstractionConfig::isInterpreted(t2.term());
    bool bothNumbers = (theory->isInterpretedConstant(t1) && theory->isInterpretedConstant(t2));

    switch(_mode) {
      case Shell::Options::UnificationWithAbstraction::OFF:
        return false;

      case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
        return t1Interp && t2Interp && !bothNumbers;

      case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
        return !bothNumbers && (t1Interp || t2Interp);

      case Shell::Options::UnificationWithAbstraction::CONSTANT:
        return  !bothNumbers 
             && (t1Interp || t2Interp)
             && (t1Interp || env.signature->functionArity(t1.term()->functor()))
             && (t2Interp || env.signature->functionArity(t2.term()->functor()));

      case Shell::Options::UnificationWithAbstraction::ALL:
      case Shell::Options::UnificationWithAbstraction::GROUND: // TODO should ground & all really behave in the same way?
        return true;

      default:
        ASSERTION_VIOLATION;
    }
}

bool UWAMismatchHandler::introduceConstraint(TermList t1,unsigned index1, TermList t2,unsigned index2)
{
  _constraints.push(make_pair(make_pair(t1,index1),make_pair(t2,index2)));
  return true;
}

bool HOMismatchHandler::handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2)
{
  CALL("HOMismatchHandler::handle");

  _constraints.push(make_pair(make_pair(t1,index1),make_pair(t2,index2)));
  return true; 
}

}
