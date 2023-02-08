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
#include "Lib/Coproduct.hpp"
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
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)

namespace Kernel
{

  
// pair<TermList, int>& TermSpec::deref()
// { return _deref.unwrapOrInit([&]() { 
//     auto t = _subs->derefBound(RobSubstitution::TermSpec(_term, _index));
//     return make_pair(t.term, t.index);
//   }); }

// TermSpec TermSpec::termArg(unsigned i)
// { return TermSpec(*_subs, term()->termArg(i), index(i + nTypeArgs())); }

// TermSpec::TermSpec(RobSubstitution& subs, TermList term, int index)
//   : _subs(&subs)
//   , _self(make_pair(term, index))
// {
// }


// TermSpec TermSpec::typeArg(unsigned i)
// { return TermSpec(*_subs, term()->typeArg(i), index(i)); }

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
  Recycled<Stack<TermSpec>> _todo;
  RobSubstitution const* _subs;
public:
  AcIter(unsigned function, TermSpec t, RobSubstitution const* subs) : _function(function), _todo(std::initializer_list<TermSpec>{ t }), _subs(subs) {  }
  DECL_ELEMENT_TYPE(TermSpec);

  bool hasNext() const { return !_todo->isEmpty(); }

  TermSpec next() {
    ASS(!_todo->isEmpty());
    while (true){
      auto t = _todo->pop().deref(_subs);
      while (t.isTerm() && t.functor() == _function) {
        ASS_EQ(t.nTermArgs(), 2);
        _todo->push(t.termArg(1));
        t = t.termArg(0);
      }
      return t;
    }
  }
};

// auto acIter(unsigned f, TermSpec t)
// { return iterTraits(AcIter(f, t)); }

bool UWAMismatchHandler::canAbstract(Shell::Options::UnificationWithAbstraction opt, TermSpec t1, TermSpec t2) const 
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
    case Shell::Options::UnificationWithAbstraction::AC2: 
      ASSERTION_VIOLATION
  }
  ASSERTION_VIOLATION;
}

// bool UWAMismatchHandler::recheck(TermSpec t1, TermSpec t2) const
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

// std::ostream& operator<<(std::ostream& out, TermSpec const& self)
// { return out << self._term << "/" << self._index << *self._subs; }

Option<MismatchHandler::AbstractionResult> UWAMismatchHandler::tryAbstract(AbstractingUnifier const* au, TermSpec t1, TermSpec t2) const
{
  CALL("UWAMismatchHandler::checkUWA");
  using Uwa = Shell::Options::UnificationWithAbstraction;


  // TODO add parameter instead of reading from options
  static Uwa opt = env.options->unificationWithAbstraction();
  if (opt == Uwa::AC1 || opt == Uwa::AC2) {
      if (!(t1.isTerm() && theory->isInterpretedFunction(t1.functor(), IntTraits::addI))
       || !(t2.isTerm() && theory->isInterpretedFunction(t2.functor(), IntTraits::addI))) {
        return Option<AbstractionResult>();
      }
      auto a1 = iterTraits(AcIter(IntTraits::addF(), t1, &au->subs())).template collect<Stack>();
      auto a2 = iterTraits(AcIter(IntTraits::addF(), t2, &au->subs())).template collect<Stack>();
      a1.sort();
      a2.sort();

      auto diff1 = iterSortedDiff(a1.iterFifo(), a2.iterFifo()).template collect<Stack>();
      auto diff2 = iterSortedDiff(a2.iterFifo(), a1.iterFifo()).template collect<Stack>();
      auto sum = [](auto& diff) {
          return iterTraits(diff.iterFifo())
            .fold([](auto l, auto r) 
              { return TermSpec(IntTraits::addF(), { l, r, }); }); };
      auto diffConstr = [&]() 
      { return UnificationConstraint(sum(diff1), sum(diff2)); };

      auto functors = [](auto& diff) 
      { return iterTraits(diff.iterFifo()).map([](auto f) { return f.functor(); }); };

      if (diff1.size() == 0 && diff2.size() == 0) {
        return some(AbstractionResult(EqualIf({}, {})));

      } else if (( diff1.size() == 0 && diff2.size() != 0 )
              || ( diff2.size() == 0 && diff1.size() != 0 ) ) {
        return some(AbstractionResult(NeverEqual{}));

      } else if (opt == Uwa::AC2 && diff1.size() == 1 && diff1[0].isVar()) {
        return some(AbstractionResult(EqualIf({ UnificationConstraint(diff1[0], sum(diff2)) }, {})));

      } else if (opt == Uwa::AC2 && diff2.size() == 1 && diff2[0].isVar()) {
        return some(AbstractionResult(EqualIf({ UnificationConstraint(diff2[0], sum(diff1)) }, {})));

      } else if (concatIters(diff1.iterFifo(), diff2.iterFifo()).any([](auto x) { return x.isVar(); })) {
        return some(AbstractionResult(EqualIf({}, {diffConstr()})));

      } else if (iterSortedDiff(functors(diff1), functors(diff2)).hasNext()
              || iterSortedDiff(functors(diff2), functors(diff1)).hasNext()) {
        return some(AbstractionResult(NeverEqual{}));

      } else {
        return some(AbstractionResult(EqualIf({}, {diffConstr()})));
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
    AbstractingUnifier const* au, 
    TermSpec t1, TermSpec t2) const
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
      auto argSort1 = t1.typeArg(0).deref(&au->subs());
      auto argSort2 = t2.typeArg(0).deref(&au->subs());
      if (t1.isVar() || t2.isVar()
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


Option<Literal*> UnificationConstraint::toLiteral(RobSubstitution& s)
{ 
  auto t1 = _t1.toTerm(s);
  auto t2 = _t2.toTerm(s);
  return t1 == t2 
    ? Option<Literal*>()
    : Option<Literal*>(Literal::createEquality(false, t1, t2, t1.isTerm() ? SortHelper::getResultSort(t1.term()) : SortHelper::getResultSort(t2.term())));
}


}


bool AbstractingUnifier::unify(TermList term1, unsigned bank1, TermList term2, unsigned bank2)
{
#define DEBUG_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
  CALL("AbstractionResult::unify");
  TermSpec t1(term1, bank1);
  TermSpec t2(term2, bank2);
  DEBUG_UNIFY(1, *this, ".unify(", TermSpec(term1, bank1), ",", TermSpec(term2, bank2), ")")

  if(t1 == t2) {
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<UnificationConstraint>> toDo;
    toDo->push(UnificationConstraint(t1, t2));
    
    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnificationConstraint>> encountered;

    Option<MismatchHandler::AbstractionResult> absRes;
    auto doAbstract = [&](auto l, auto r) -> bool
    { 
      if (!_uwa) return false;
      absRes = _uwa->tryAbstract(this, l, r);
      return absRes.isSome();
    };

    auto pushTodo = [&](auto pair) {
        // we unify each subterm pair at most once, to avoid worst-case exponential runtimes
        // in order to safe memory we do ot do this for variables.
        // (Note by joe:  didn't make this decision, but just keeping the implemenntation 
        // working as before. i.e. as described in the paper "Comparing Unification 
        // Algorithms in First-Order Theorem Proving", by Krystof and Andrei)
        // TODO restore this branch?
        // if (pair.first.isVar() && isUnbound(getVarSpec(pair.first)) &&
        //     pair.second.isVar() && isUnbound(getVarSpec(pair.second))) {
        //   toDo.push(pair);
        // } else 
        if (!encountered->find(pair)) {
          encountered->insert(pair);
          toDo->push(pair);
        }
    };

    auto occurs = [this](auto var, auto term) {
      Recycled<Stack<TermSpec>> todo;
      todo->init({ term });
      while (todo->isNonEmpty()) {
        auto t = todo->pop().deref(&subs());
        if (t.isVar()) {
          if (t == var) {
            return true;
          }
        } else {
          todo->loadFromIterator(t.allArgs());
        }
      }
      return false;
    };


    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      auto dt1 = x.lhs().deref(&subs());
      auto dt2 = x.rhs().deref(&subs());
      if (dt1 == dt2) {

      } else if(dt1.isVar() && !occurs(dt1, dt2)) {
        subs().bind(dt1.varSpec(), dt2);

      } else if(dt2.isVar() && !occurs(dt2, dt1)) {
        subs().bind(dt2.varSpec(), dt1);

      } else if(doAbstract(dt1, dt2)) {

        ASS(absRes);
        if (absRes->is<MismatchHandler::NeverEqual>()) {
          return false;

        } else {
          ASS(absRes->is<MismatchHandler::EqualIf>())
          auto& conditions = absRes->unwrap<MismatchHandler::EqualIf>();
          for (auto& x : *conditions.unify) {
            pushTodo(std::move(x));
          }
          for (auto& x: *conditions.constraints) {
            add(std::move(x));
          }
        }

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.functor() == dt2.functor()) {
        
        for (auto c : dt1.allArgs().zip(dt2.allArgs())) {
          pushTodo(UnificationConstraint(c.first, c.second));
        }

      } else {
        return false;
      }

    }
    return true;
  };

  BacktrackData localBD;
  bdRecord(localBD);
  bool success = impl();
  bdDone();

  if(!success) {
    localBD.backtrack();
  } else {
    if(subs().bdIsRecording()) {
      subs().bdCommit(localBD);
    }
    localBD.drop();
  }

  DEBUG_UNIFY(1, *this)
  return success;
}
