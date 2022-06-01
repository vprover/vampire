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
#include "Kernel/SortHelper.hpp"
#include "Inferences/PolynomialEvaluation.hpp"


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "Kernel/NumTraits.hpp"

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

    auto ircAbsractCoarse = [&](auto t) { 
      if (t.isTerm()) {
        auto f = t.term()->functor();
        return forAnyNumTraits([&](auto numTraits) {
            using NumTraits = decltype(numTraits);
            return f == NumTraits::addF()  // t == ( t1 + t2 )
               || (f == NumTraits::mulF() && ( t.term()->nthArgument(0)->isVar() || t.term()->nthArgument(1)->isVar() ));// t == ( x * t1 ) or t == ( t1 * x )
        });
      } else {
        return false;
      }
    };

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

      case Shell::Options::UnificationWithAbstraction::IRC1: 
        return ircAbsractCoarse(t1) || ircAbsractCoarse(t2);

      case Shell::Options::UnificationWithAbstraction::IRC2:  {
        auto sort = SortHelper::getResultSort(t1.term());
        return (ircAbsractCoarse(t1) || ircAbsractCoarse(t2)) && forAnyNumTraits([&](auto numTraits){
            using NumTraits = decltype(numTraits);
            if (NumTraits::sort() != sort) return false;
            // TODO get the polynomial evaluation instance less dirty
            static Inferences::PolynomialEvaluation ev;
            auto sub = ev.evaluateToTerm(NumTraits::add( NumTraits::minus(t1), t2).term());
            //   ^^^--> `t2 - t1`
            return !sub.ground() || sub == NumTraits::zero();
        });
      }

      case Shell::Options::UnificationWithAbstraction::IRC3:  {
        // auto sort = SortHelper::getResultSort(t1.term());
        auto isAdd = [&](Term* t) {
          auto f = t->functor();
          return forAnyNumTraits([&](auto numTraits) {
              return f == numTraits.addF();
          });
        };

        auto isNumMul = [&](Term* t) {
          auto f = t->functor();
          return forAnyNumTraits([&](auto numTraits) {
              using NumTraits = decltype(numTraits);
              return f == NumTraits::mulF() && ( numTraits.isNumeral(*t->nthArgument(0)) ||  numTraits.isNumeral(*t->nthArgument(1)) );
          });
        };

        auto isVarMul = [&](Term* t) {
          auto f = t->functor();
          return forAnyNumTraits([&](auto numTraits) {
              using NumTraits = decltype(numTraits);
              return f == NumTraits::mulF() && ( t->nthArgument(0)->isVar() ||  t->nthArgument(1)->isVar() );
          });
        };

        auto s = t1.term();
        auto t = t2.term();
        return (isAdd(s) && isAdd(t)) 
            || isVarMul(s) || isVarMul(t);
            // || (isNumMul(s) && isNumMul(t));

      }
    }
    ASSERTION_VIOLATION;
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
