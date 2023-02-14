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
#include "Kernel/LASCA.hpp"
#include "Kernel/QKbo.hpp"


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


bool occursUncancellable(unsigned var, Term* t) {
  ASS(t->containsSubterm(TermList::var(var)))
  if (t->isSort()) return true; // <- for sorts arguments might never cancel out
  Stack<TermList>* todo;
  Recycler::get(todo);
  todo->reset();
  todo->push(TermList(t));
  while (!todo->isEmpty()) {
    auto t = todo->pop();
    if (t.isTerm()) {
      auto f = t.term()->functor();
      auto argsMightCancel = forAnyNumTraits([&](auto n){
            // check if its subterms might cancel out
            return n.isAdd(f) || n.isMul(f);
         });
      if (!argsMightCancel) {
        todo->loadFromIterator(termArgIter(t.term()));
      }
    } else if (t.isVar() && var == t.var()) {
      Recycler::release(todo);
      return true;
    }
  }
  Recycler::release(todo);
  return false;
}

bool UWAMismatchHandler::checkUWA(TermList t1, TermList t2)
{
  CALL("UWAMismatchHandler::checkUWA");
  if (t1.isVar()) return !occursUncancellable(t1.var(), t2.term());
  if (t2.isVar()) return !occursUncancellable(t2.var(), t1.term());

    // if(!(t1.isTerm() && t2.isTerm())) return false;

    bool t1Interp = t1.isTerm() && Shell::UnificationWithAbstractionConfig::isInterpreted(t1.term());
    bool t2Interp = t2.isTerm() && Shell::UnificationWithAbstractionConfig::isInterpreted(t2.term());
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

    // TODO get rid of globalState
    auto shared = LascaState::globalState;
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

      case Shell::Options::UnificationWithAbstraction::LASCA1: 
        return ircAbsractCoarse(t1) || ircAbsractCoarse(t2);

      case Shell::Options::UnificationWithAbstraction::LASCA2:  {
        return (ircAbsractCoarse(t1) || ircAbsractCoarse(t2)) 
          && !shared->equivalent(t1, t2);
      }

      case Shell::Options::UnificationWithAbstraction::LASCA4:  {

        TIME_TRACE("unification with abstraction LASCA4")


        if (t1.isVar() && t2.isVar()) return true;
        TermList sort;
        if (t1.isTerm() && t2.isTerm()) {
          sort = SortHelper::getResultSort(t1.term());
          if (SortHelper::getResultSort(t2.term()) != sort) {
            return false;
          }

        } else {
          sort = t1.isTerm() ? SortHelper::getResultSort(t1.term()) 
                             : SortHelper::getResultSort(t2.term());
        }

        if (!shared->interpretedFunction(t1) && !shared->interpretedFunction(t2))
          return false;

        auto canAbstract = forAnyNumTraits([&](auto numTraits) {
            if (numTraits.sort() == sort) {
                auto a1 = shared->signedAtoms<decltype(numTraits)>(t1);
                auto a2 = shared->signedAtoms<decltype(numTraits)>(t2);

                if (a1.isNone() || a2.isNone()) 
                  return Option<bool>(true);

                // we have s or t being a sum `k x + ... `
                if (concatIters(a1.unwrap().elems.iter(), a2.unwrap().elems.iter())
                       .any([&](auto& x) { return get<0>(x).term.isVar(); }))
                  return Option<bool>(true);

                return Option<bool>(Ordering::Result::EQUAL == OrderingUtils2::weightedMulExt(
                    a1.unwrap(),
                    a2.unwrap(),
                    [](auto& l, auto& r) { return (l.sign == r.sign && l.term.term()->functor() == r.term.term()->functor())
                      ? Ordering::Result::EQUAL
                      : Ordering::Result::INCOMPARABLE; }));
            } else {
                return Option<bool>();
            }
        });

        return canAbstract.unwrap();
      }

      case Shell::Options::UnificationWithAbstraction::LASCA3:  {
        // auto sort = SortHelper::getResultSort(t1.term());
        auto isAdd = [&](Term* t) {
          auto f = t->functor();
          return forAnyNumTraits([&](auto numTraits) {
              return f == numTraits.addF();
          });
        };

        // auto isNumMul = [&](Term* t) {
        //   auto f = t->functor();
        //   return forAnyNumTraits([&](auto numTraits) {
        //       using NumTraits = decltype(numTraits);
        //       return f == NumTraits::mulF() && ( numTraits.isNumeral(*t->nthArgument(0)) ||  numTraits.isNumeral(*t->nthArgument(1)) );
        //   });
        // };

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
