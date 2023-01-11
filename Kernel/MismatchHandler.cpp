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

  

bool MismatchHandlerTerm::isNormalVar()
{ return derefTerm().isVar() && !derefTerm().isSpecialVar(); }

unsigned MismatchHandlerTerm::normalVarNumber()
{ return derefTerm().var(); }

bool MismatchHandlerTerm::isSpecialVar()
{ return derefTerm().isSpecialVar(); }

bool MismatchHandlerTerm::isTerm()
{ return derefTerm().isTerm(); }

bool MismatchHandlerTerm::isSort()
{ return derefTerm().term()->isSort(); }

unsigned MismatchHandlerTerm::functor()
{ return derefTerm().term()->functor(); }

unsigned MismatchHandlerTerm::nTypeArgs()
{ return derefTerm().term()->numTypeArguments(); }

unsigned MismatchHandlerTerm::nTermArgs()
{ return derefTerm().term()->numTermArguments(); }

bool MismatchHandlerTerm::isNumeral()
{ return derefTerm().isTerm() && env.signature->getFunction(functor())->numericConstant(); }

bool MismatchHandlerTerm::isGround()
{ return _subs.apply(_term, _index).ground(); }

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

bool UWAMismatchHandler::recheck(MismatchHandlerTerm t1, MismatchHandlerTerm t2) const
{ 
  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
  if (opt == Shell::Options::UnificationWithAbstraction::GROUND) {
    return (t1.isGround() && t2.isGround()) && (isInterpreted(t1.functor()) || isInterpreted(t2.functor()));
  } else {
    return canAbstract(t1, t2); 
  }
}

std::ostream& operator<<(std::ostream& out, MismatchHandlerTerm const& self)
{ return out << self._term << "/" << self._index << self._subs; }

bool UWAMismatchHandler::tryAbstract(
      MismatchHandlerTerm t1, MismatchHandlerTerm t2,
      AbstractingUnifier& constr) const
{
  CALL("UWAMismatchHandler::checkUWA");

  auto abs = canAbstract(t1, t2);
  DEBUG("canAbstract(", t1, ",", t2, ") = ", abs);
  if (abs) {
    constr.add(UnificationConstraint(t1, t2));
  }
  return abs;
}

bool HOMismatchHandler::tryAbstract(
    MismatchHandlerTerm t1, MismatchHandlerTerm t2,
    AbstractingUnifier& au) const
{
  CALL("HOMismatchHandler::tryAbstract")
  ASS(t1.isTerm() || t2.isTerm())

  // auto isRightApp = [](auto& t) { return  }
  auto isApp = [](auto& t) { return env.signature->isAppFun(t.functor()); };
  // if (t1.isSpecialVar()) { 
  //   au.waitFor(t1.specialVarNumber(), Action(isRightApp)); 
  // };
  ASS_REP(!t1.isSpecialVar(), "TODO")
  ASS_REP(!t2.isSpecialVar(), "TODO")
  if ( (t1.isTerm() && t1.isSort()) 
    || (t2.isTerm() && t2.isSort()) ) return false;
  if (t1.isTerm() && t2.isTerm()) {
    if (isApp(t1) && isApp(t2)) {
      auto argSort1 = t1.typeArg(0);
      auto argSort2 = t2.typeArg(0);
      ASS_REP(!argSort1.isSpecialVar(), "TODO")
      ASS_REP(!argSort2.isSpecialVar(), "TODO")
      if (t1.isNormalVar() || t2.isNormalVar()
       || env.signature->isArrowCon(argSort1.functor())
       || env.signature->isArrowCon(argSort2.functor())
       ) {
        au.add(UnificationConstraint(t1.termArg(1), t2.termArg(1)));
        return true;
      }
    }
  }
  return false;
  // ASS(t1.isTerm() || t2.isTerm())

  // if (t1.isNormalVar() || t2.term.isVar()) return false;
  ASSERTION_VIOLATION_REP("TODO");
  // if (t1.term.isVar() || t2.term.isVar()) return false;
  // if (t1.term.isApplication() && t2.term.isApplication()) {
  //   SortHelper::getResultSort(t1.term.term())
  // }
  // auto t1 = subs.apply(o1, i1);
  // auto t2 = subs.apply(o2, i2);
  // ASS(!t1.isSpecialVar() && !t2.isSpecialVar())
  // if (t1.isNormalVar() || t1.isNormalVar()) return false;
  // if (!t1.isApplication() || !t2.isApplication()) {
  //   return false;
  // }
  //
  //
  // auto arrowArgIter = [](auto arrowSort) {
  //   return [iter = TermList(arrowSort)]() mutable {
  //     ASS(iter.isTerm() && iter.isArrowSort());
  //     auto arg = *iter.term()->nthArgument(0);
  //     iter = *iter.term()->nthArgument(1);
  //     return arg;
  //   };
  // };
  // DBGE(t1)
  // DBGE(t2)
  // ApplicativeArgsIt iter1(t1, false);
  // auto sortIter1 = arrowArgIter(iter1.headSort());
  // ApplicativeArgsIt iter2(t2, false);
  // auto sortIter2 = arrowArgIter(iter2.headSort());
  //
  // Recycled<Stack<pair<TermList, TermList>>> cs;
  // Recycled<Stack<pair<TermList, TermList>>> unifs;
  // while (iter1.hasNext() && iter2.hasNext()) {
  //   auto t1 = iter1.next();
  //   auto t2 = iter2.next();
  //   auto s1 = sortIter1();
  //   auto s2 = sortIter2();
  //   if (s1.isArrowSort() || s2.isArrowSort()
  //       || s1 == AtomicSort::boolSort() || s2 == AtomicSort::boolSort()) {
  //     cs->push(make_pair(t1,t2));
  //   } else {
  //     unifs->push(make_pair(t1,t2));
  //   }
  // }
  // if (iter1.hasNext() || iter2.hasNext()) {
  //   return false;
  // }
  // if (unifs->isNonEmpty())
  //   {ASSERTION_VIOLATION_REP("TODO unifs need to be added to unifications")}
  // DBGE(cs)
  // DBGE(unifs)
  // for (auto& c : iterTraits(cs->iter())) {
  //   au.addConstraint(UnificationConstraint(c.first, RobSubstitution::UNBOUND_INDEX, c.second,  RobSubstitution::UNBOUND_INDEX));
  // }
  // return true;
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
