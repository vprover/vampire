
/*
 * File MismatchHandler.cpp.
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

    bool t1Interp = (theory->isInterpretedFunction(t1) || theory->isInterpretedConstant(t1));
    bool t2Interp = (theory->isInterpretedFunction(t2) || theory->isInterpretedConstant(t2));
    bool bothNumbers = (theory->isInterpretedConstant(t1) && theory->isInterpretedConstant(t2));

    bool okay = true;
   
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
        case Shell::Options::UnificationWithAbstraction::FIXED:
        case Shell::Options::UnificationWithAbstraction::GROUND:
          break;
        default:
          ASSERTION_VIOLATION;
      }
   return okay;
}

bool UWAMismatchHandler::introduceConstraint(RobSubstitution* subst,TermList t1,unsigned index1, TermList t2,unsigned index2)
{
  auto constraint = make_pair(make_pair(t1,index1),make_pair(t2,index2));
  constraints.push(constraint);
  return true;
}

}
