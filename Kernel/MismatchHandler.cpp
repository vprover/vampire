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

#include "Lib/Backtrackable.hpp"
#include "Shell/Options.hpp"
#include "Lib/Environment.hpp"


#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"

#include "MismatchHandler.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel
{

  
pair<TermList, int>& MismatchHandlerTerm::deref()
{ return _deref.unwrapOrInit([&]() { 
    auto t = _subs.derefBound(RobSubstitution::TermSpec(_term, _index));
    return make_pair(t.term, t.index);
  }); }

MismatchHandlerTerm MismatchHandlerTerm::termArg(unsigned i)
{ return MismatchHandlerTerm(_subs, derefTerm().term()->termArg(i), _index); }

MismatchHandlerTerm::MismatchHandlerTerm(RobSubstitution& subs, TermList term, int index)
  : _subs(subs)
  , _term(term)
  , _index(index)
  , _deref() 
{
}


MismatchHandlerTerm MismatchHandlerTerm::typeArg(unsigned i)
{ return MismatchHandlerTerm(_subs, derefTerm().term()->typeArg(i), _index); }

unique_ptr<MismatchHandler> MismatchHandler::create()
{
  if (env.options->unificationWithAbstraction()!=Options::UnificationWithAbstraction::OFF) {
    return make_unique<UWAMismatchHandler>();
  } else if (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION && env.property->higherOrder()) { 
    // TODO  ask ahmed: are this the corret options for higher order abstraction
    return make_unique<HOMismatchHandler>();
  } else {
    return unique_ptr<MismatchHandler>();
  }
}

unique_ptr<MismatchHandler> MismatchHandler::createOnlyHigherOrder()
{
  if (env.options->functionExtensionality() == Options::FunctionExtensionality::ABSTRACTION && env.property->higherOrder()) { 
    // TODO  ask ahmed: are this the corret options for higher order abstraction
    return make_unique<HOMismatchHandler>();
  } else {
    return unique_ptr<MismatchHandler>();
  }
}

bool UWAMismatchHandler::isInterpreted(unsigned functor) const 
{
  auto f = env.signature->getFunction(functor);
  return f->interpreted() || f->termAlgebraCons();
}

bool UWAMismatchHandler::canAbstract(MismatchHandlerTerm t1, MismatchHandlerTerm t2) const 
{

  if(!(t1.isTerm() && t2.isTerm())) return false;
  if(t1.isSort() || t2.isSort()) return false;

  bool t1Interp = isInterpreted(t1.functor());
  bool t2Interp = isInterpreted(t2.functor());
  bool bothNumbers = t1.isNumeral() && t2.isNumeral();

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
      okay &= (t1Interp || t1.nTermArgs());
      okay &= (t2Interp || t2.nTermArgs());
      break; 
    case Shell::Options::UnificationWithAbstraction::ALL:
    case Shell::Options::UnificationWithAbstraction::GROUND:
      break;
    default:
      ASSERTION_VIOLATION;
  }
  return okay;

}

// bool UWAMismatchHandler::recheck(MismatchHandlerTerm t1, MismatchHandlerTerm t2) const
// { 
//   static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
//   if (opt == Shell::Options::UnificationWithAbstraction::GROUND) {
//     return (t1.isGround() && t2.isGround()) && (isInterpreted(t1.functor()) || isInterpreted(t2.functor()));
//   } else {
//     return canAbstract(t1, t2); 
//   }
// }

std::ostream& operator<<(std::ostream& out, MismatchHandlerTerm const& self)
{ return out << self._term << "/" << self._index << self._subs; }

Option<MismatchHandler::AbstractionResult> UWAMismatchHandler::tryAbstract(MismatchHandlerTerm t1, MismatchHandlerTerm t2) const
{
  CALL("UWAMismatchHandler::checkUWA");

  auto abs = canAbstract(t1, t2);
  DEBUG("canAbstract(", t1, ",", t2, ") = ", abs);
  return someIf(abs, [&](){
      return AbstractionResult(EqualIf(
            {},
            { UnificationConstraint(t1, t2) }
            ));
  });
}

Option<MismatchHandler::AbstractionResult> HOMismatchHandler::tryAbstract(
    MismatchHandlerTerm t1, MismatchHandlerTerm t2) const
{
  CALL("HOMismatchHandler::tryAbstract")
  ASS(t1.isTerm() || t2.isTerm())
  ASS(!t1.isSpecialVar())
  ASS(!t2.isSpecialVar())

  auto isApp = [](auto& t) { return env.signature->isAppFun(t.functor()); };
  if ( (t1.isTerm() && t1.isSort()) 
    || (t2.isTerm() && t2.isSort()) ) return Option<AbstractionResult>();
  if (t1.isTerm() && t2.isTerm()) {
    if (isApp(t1) && isApp(t2)) {
      auto argSort1 = t1.typeArg(0);
      auto argSort2 = t2.typeArg(0);
      if (t1.isAnyVar() || t2.isAnyVar()
       || env.signature->isArrowCon(argSort1.functor())
       || env.signature->isArrowCon(argSort2.functor())
       ) {
        return some(AbstractionResult(EqualIf(
              { UnificationConstraint(t1.termArg(0), t2.termArg(0)) },
              { UnificationConstraint(t1.termArg(1), t2.termArg(1)) })));
      }
    }
  }
  return Option<AbstractionResult>();
}

void UnificationConstraintStack::add(UnificationConstraint c, Option<BacktrackData&> bd)
{ 
  DEBUG("introduced constraing: ", c)
  if (bd) {
    _cont.backtrackablePush(std::move(c), *bd); 
  } else {
    _cont.push(std::move(c));
  }
}

Recycled<Stack<Literal*>> UnificationConstraintStack::literals(RobSubstitution& s)
{ 
  Recycled<Stack<Literal*>> out;
  out->reserve(_cont.size());
  out->loadFromIterator(literalIter(s));
  return out;
}


Option<Literal*> UnificationConstraint::toLiteral(RobSubstitution& s) const
{ 
  auto t1 = s.apply(_term1, _index1);
  auto t2 = s.apply(_term2, _index2);
  return t1 == t2 
    ? Option<Literal*>()
    : Option<Literal*>(Literal::createEquality(false, t1, t2, t1.isTerm() ? SortHelper::getResultSort(t1.term()) : SortHelper::getResultSort(t2.term())));
}


}
