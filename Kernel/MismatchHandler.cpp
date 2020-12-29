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

namespace Kernel
{

bool UWAMismatchHandler::handle(RobSubstitution* sub, TermList t1, unsigned index1, TermList t2, unsigned index2)
{
  CALL("UWAMismatchHandler::handle");

    TermList tt1 = sub->apply(t1,index1);
    TermList tt2 = sub->apply(t2,index2);

  if(checkUWA(tt1,tt2)){
    return introduceConstraint(sub,t1,index1,t2,index2);
  }
  return false;
}

bool UWAMismatchHandler::checkUWA(TermList t1, TermList t2)
{
  CALL("UWAMismatchHandler::checkUWA");

    if(!(t1.isTerm() && t2.isTerm())) return false;
    ASS_NEQ(t1, t2);

    bool t1Interp = theory->isInterpretedFunction(t1);
    bool t2Interp = theory->isInterpretedFunction(t2);
    /* for distinct constants it does not make sense to abstract, because c1 != c2 will always be evaluated to true */
    bool bothDistinctConstants = (theory->isInterpretedConstant(t1) && theory->isInterpretedConstant(t2)); 

    static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
      switch(opt){
        case Shell::Options::UnificationWithAbstraction::OFF:
          return false;
        case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
          return (t1Interp && t2Interp && !bothDistinctConstants);
        case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
          return !bothDistinctConstants && (t1Interp || t2Interp);
        case Shell::Options::UnificationWithAbstraction::CONSTANT:
          return !bothDistinctConstants && (t1Interp || t2Interp)
            && (t1Interp || env.signature->functionArity(t1.term()->functor()))
            && (t2Interp || env.signature->functionArity(t2.term()->functor()));
        case Shell::Options::UnificationWithAbstraction::ALL:
          return true;
        case Shell::Options::UnificationWithAbstraction::GROUND:
          return true;
      }
      ASSERTION_VIOLATION
}

bool UWAMismatchHandler::introduceConstraint(RobSubstitution* subst,TermList t1,unsigned index1, TermList t2,unsigned index2)
{
  auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
  constraints.push(constraint);
  return true;
}

}
