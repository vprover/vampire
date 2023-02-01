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
#include "NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel
{

  
pair<TermList, int>& MismatchHandlerTerm::deref()
{ return _deref.unwrapOrInit([&]() { 
    auto t = _subs->derefBound(RobSubstitution::TermSpec(_term, _index));
    return make_pair(t.term, t.index);
  }); }

MismatchHandlerTerm MismatchHandlerTerm::termArg(unsigned i)
{ return MismatchHandlerTerm(*_subs, derefTerm().term()->termArg(i), _index); }

MismatchHandlerTerm::MismatchHandlerTerm(RobSubstitution& subs, TermList term, int index)
  : _subs(&subs)
  , _term(term)
  , _index(index)
  , _deref() 
{
}


MismatchHandlerTerm MismatchHandlerTerm::typeArg(unsigned i)
{ return MismatchHandlerTerm(*_subs, derefTerm().term()->typeArg(i), _index); }

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


class AcIter {
  unsigned _function;
  Recycled<Stack<MismatchHandlerTerm>> _todo;
public:
  AcIter(unsigned function, MismatchHandlerTerm t) : _function(function), _todo(std::initializer_list<MismatchHandlerTerm>{ t }) {  }
  DECL_ELEMENT_TYPE(MismatchHandlerTerm);

  bool hasNext() const { return !_todo->isEmpty(); }

  MismatchHandlerTerm next() {
    ASS(!_todo->isEmpty());
    while (true){
      auto t = _todo->pop();
      while (t.isTerm() && t.functor() == _function) {
        ASS_EQ(t.nTermArgs(), 2);
        _todo->push(t.termArg(1));
        t = t.termArg(0);
      }
      return t;
    }
  }
};

auto acIter(unsigned f, MismatchHandlerTerm t)
{ return iterTraits(AcIter(f, t)); }

bool UWAMismatchHandler::canAbstract(Shell::Options::UnificationWithAbstraction opt, MismatchHandlerTerm t1, MismatchHandlerTerm t2) const 
{

  if(!(t1.isTerm() && t2.isTerm())) return false;
  if(t1.isSort() || t2.isSort()) return false;

  bool t1Interp = isInterpreted(t1.functor());
  bool t2Interp = isInterpreted(t2.functor());
  bool bothNumbers = t1.isNumeral() && t2.isNumeral();

  switch(opt) {
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
      return (t1Interp && t2Interp && !bothNumbers);
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      return !bothNumbers && (t1Interp || t2Interp);
      break;
    case Shell::Options::UnificationWithAbstraction::CONSTANT:
      return !bothNumbers && (t2Interp || t2Interp)
            && (t1Interp || t1.nTermArgs())
            && (t2Interp || t2.nTermArgs());
    case Shell::Options::UnificationWithAbstraction::ALL:
    case Shell::Options::UnificationWithAbstraction::GROUND:
      return true;
    case Shell::Options::UnificationWithAbstraction::OFF:
      return false;
    case Shell::Options::UnificationWithAbstraction::AC1: 
      ASSERTION_VIOLATION
  }
  ASSERTION_VIOLATION;
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
//

// struct SortedIterDiff {
//
// };
//
// template<class A>
// auto iterDiff(Stack<A> const&,Stack<A> const&)
// {
//
// }

std::ostream& operator<<(std::ostream& out, MismatchHandlerTerm const& self)
{ return out << self._term << "/" << self._index << *self._subs; }

Option<MismatchHandler::AbstractionResult> UWAMismatchHandler::tryAbstract(MismatchHandlerTerm t1, MismatchHandlerTerm t2) const
{
  CALL("UWAMismatchHandler::checkUWA");


  // TODO add parameter instead of reading from options
  static Shell::Options::UnificationWithAbstraction opt = env.options->unificationWithAbstraction();
  if (opt == Shell::Options::UnificationWithAbstraction::AC1) {
      if (!(t1.isTerm() && theory->isInterpretedFunction(t1.functor(), IntTraits::addI))
       || !(t2.isTerm() && theory->isInterpretedFunction(t2.functor(), IntTraits::addI))) {
        return Option<AbstractionResult>();
      }
      auto a1 = acIter(IntTraits::addF(), t1).template collect<Stack>();
      auto a2 = acIter(IntTraits::addF(), t2).template collect<Stack>();
      a1.sort();
      a2.sort();

      auto collectDiffSyms = [](auto const& lhs, auto const& rhs) {
        Stack<unsigned> diffSym;
        for (auto a : iterSortedDiff(lhs.iterFifo(), rhs.iterFifo())) {
          if (a.isAnyVar()) {
            return Option<decltype(diffSym)>(); //some(AbstractionResult(EqualIf({}, {UnificationConstraint(t1, t2)})));
          } else {
            diffSym.push(a.functor());
          }
        }
        return some(std::move(diffSym));
      };

      auto diff1 = collectDiffSyms(a1, a2);
      if (!diff1) return some(AbstractionResult(EqualIf({}, {UnificationConstraint(t1, t2)})));
      auto diff2 = collectDiffSyms(a2, a1);
      if (!diff2) return some(AbstractionResult(EqualIf({}, {UnificationConstraint(t1, t2)})));

      if (diff1->size() == 0 && diff2->size() == 0) {
        return some(AbstractionResult(EqualIf({}, {})));

      } else if (iterSortedDiff(diff1->iterFifo(), diff2->iterFifo()).hasNext()
              || iterSortedDiff(diff2->iterFifo(), diff1->iterFifo()).hasNext()) {
        return some(AbstractionResult(NeverEqual{}));

      } else {
        return some(AbstractionResult(EqualIf({}, {UnificationConstraint(t1, t2)})));
      }


  } else {
    auto abs = canAbstract(opt, t1, t2);
    DEBUG("canAbstract(", t1, ",", t2, ") = ", abs);
    return someIf(abs, [&](){
        return AbstractionResult(EqualIf(
              {},
              { UnificationConstraint(t1, t2) }
              ));
    });
  }
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
    backtrackablePush(_cont, std::move(c), *bd); 
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
