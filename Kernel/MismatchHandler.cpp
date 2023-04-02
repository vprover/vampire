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
#include "Lib/BiMap.hpp"

#include "Forwards.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "RobSubstitution.hpp"
#include "SortHelper.hpp"

#include "MismatchHandler.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "NumTraits.hpp"
#include "Kernel/TermIterators.hpp"
#include "Debug/Output.hpp"
#define DEBUG(...) // DBG(__VA_ARGS__)
#define DEBUG_FINALIZE(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)

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

Shell::Options::UnificationWithAbstraction MismatchHandler::create()
{
  return env.options->unificationWithAbstraction();
}

bool MismatchHandler::isInterpreted(unsigned functor) const 
{
  auto f = env.signature->getFunction(functor);
  return f->interpreted() || f->termAlgebraCons();
}

class AcIter {
  unsigned _function;
  Recycled<Stack<TermSpec>> _todo;
  RobSubstitution const* _subs;
public:
  AcIter(unsigned function, TermSpec t, RobSubstitution const* subs) : _function(function), _todo(), _subs(subs) 
  { _todo->push(std::move(t)); }

  DECL_ELEMENT_TYPE(TermSpec);

  bool hasNext() const { return !_todo->isEmpty(); }

  TermSpec next() {
    ASS(!_todo->isEmpty());
    auto t = _todo->pop();
    auto* dt = &t.deref(_subs);
    while (dt->isTerm() && dt->functor() == _function) {
      ASS_EQ(dt->nTermArgs(), 2);
      _todo->push(dt->termArg(1));
      t = dt->termArg(0);
      dt = &t.deref(_subs);
    }
    return dt->clone();
  }
};

// auto acIter(unsigned f, TermSpec t)
// { return iterTraits(AcIter(f, t)); }

bool MismatchHandler::canAbstract(TermSpec const& t1, TermSpec const& t2) const 
{

  if(!(t1.isTerm() && t2.isTerm())) return false;
  if(t1.isSort() || t2.isSort()) return false;

  bool t1Interp = isInterpreted(t1.functor());
  bool t2Interp = isInterpreted(t2.functor());
  bool bothNumbers = t1.isNumeral() && t2.isNumeral();

  switch(_mode) {
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

Option<MismatchHandler::AbstractionResult> MismatchHandler::tryAbstract(RobSubstitution* sub, TermSpec const& t1, TermSpec const& t2) const
{
  CALL("MismatchHandler::checkUWA");
  using Uwa = Shell::Options::UnificationWithAbstraction;
  ASS(_mode != Uwa::OFF)


  // TODO add parameter instead of reading from options
  if (_mode == Uwa::AC1 || _mode == Uwa::AC2) {
    if (!(t1.isTerm() && theory->isInterpretedFunction(t1.functor(), IntTraits::addI))
     || !(t2.isTerm() && theory->isInterpretedFunction(t2.functor(), IntTraits::addI))) {
      return Option<AbstractionResult>();
    }
    auto a1 = iterTraits(AcIter(IntTraits::addF(), t1.clone(), sub)).template collect<Stack>();
    auto a2 = iterTraits(AcIter(IntTraits::addF(), t2.clone(), sub)).template collect<Stack>();
    auto cmp = [&](TermSpec const& lhs, TermSpec const& rhs) { return TermSpec::compare(lhs, rhs, [&](auto& t) -> TermSpec const& { return t.deref(sub); }); };
    auto less = [&](TermSpec const& lhs, TermSpec const& rhs) { return cmp(lhs, rhs) < 0; };
    a1.sort(less);
    a2.sort(less);
    // a1.sort();
    // a2.sort();

    Recycled<Stack<TermSpec>> diff1_;
    Recycled<Stack<TermSpec>> diff2_;
    auto& diff1 = *diff1_;
    auto& diff2 = *diff2_;
    diff1.moveFromIterator(iterSortedDiff(arrayIter(a1), arrayIter(a2), cmp).map([](auto& x) -> TermSpec { return x.clone(); }));
    diff2.moveFromIterator(iterSortedDiff(arrayIter(a2), arrayIter(a1), cmp).map([](auto& x) -> TermSpec { return x.clone(); }));
    auto sum = [](auto& diff) {
        return arrayIter(diff)
          .map([](auto& x) { return x.clone(); })
          .fold([](auto l, auto r) 
            { return TermSpec(IntTraits::addF(), std::move(l), std::move(r)); })
          .unwrap(); };
    auto diffConstr = [&]() 
    { return UnificationConstraint(sum(diff1), sum(diff2)); };

    auto functors = [](auto& diff) 
    { return arrayIter(diff).map([](auto& f) { return f.functor(); }); };

    if (diff1.size() == 0 && diff2.size() == 0) {
      return some(AbstractionResult(EqualIf()));

    } else if (( diff1.size() == 0 && diff2.size() != 0 )
            || ( diff2.size() == 0 && diff1.size() != 0 ) ) {
      return some(AbstractionResult(NeverEqual{}));

    } else if (_mode == Uwa::AC2 && diff1.size() == 1 && diff1[0].isVar()) {
      return some(AbstractionResult(EqualIf().unify(UnificationConstraint(std::move(diff1[0]), sum(diff2)))));

    } else if (_mode == Uwa::AC2 && diff2.size() == 1 && diff2[0].isVar()) {
      return some(AbstractionResult(EqualIf().unify(UnificationConstraint(std::move(diff2[0]), sum(diff1)))));

    } else if (concatIters(arrayIter(diff1), arrayIter(diff2)).any([](auto& x) { return x.isVar(); })) {
      return some(AbstractionResult(EqualIf().constr(diffConstr())));

    } else if (iterSortedDiff(functors(diff1), functors(diff2)).hasNext()
            || iterSortedDiff(functors(diff2), functors(diff1)).hasNext()) {
      return some(AbstractionResult(NeverEqual{}));

    } else {
      return some(AbstractionResult(EqualIf().constr(diffConstr())));
    }
  } else {
    auto abs = canAbstract(t1, t2);
    DEBUG("canAbstract(", t1, ",", t2, ") = ", abs);
    return someIf(abs, [&](){
        return AbstractionResult(EqualIf().constr(UnificationConstraint(t1.clone(), t2.clone())));
    });
  }
}

namespace UnificationAlgorithms {


bool AbstractingUnification::fixedPointIteration(RobSubstitution* sub)
{
  CALL("AbstractingUnification::fixedPointIteration");
  Recycled<Stack<UnificationConstraint>> todo;
  while (!sub->emptyConstraints()) { 
    todo->push(sub->popConstraint());
  }

  DEBUG_FINALIZE(1, "finalizing: ", todo)
  while (!todo->isEmpty()) {
    auto c = todo->pop();
    DEBUG_FINALIZE(2, "popped: ", c);
    bool progress;
    auto res = unify(c.lhs().clone(), c.rhs().clone(), progress, sub);
    if (!res) {
      DEBUG_FINALIZE(1, "finalizing failed");
      return false;
    } else if (progress) {
      while (!sub->emptyConstraints()) { 
        todo->push(sub->popConstraint());
      }
    } else {
      // no progress. we keep the constraints
    }
  }
  DEBUG_FINALIZE(1, "finalizing successful: ", *sub);
  return true;
}

bool AbstractingUnification::unify(TermList term1, unsigned bank1, TermList term2, unsigned bank2, RobSubstitution* sub)
{
  ASS(_uwa._mode != Shell::Options::UnificationWithAbstraction::OFF); 

  bool progress;
  return unify(TermSpec(term1, bank1), TermSpec(term2, bank2), progress, sub);
}

SubstIterator AbstractingUnification::unifiers(TermList t1, int index1, TermList t2, int index2, RobSubstitution* sub, bool topLevelCheck)
{
  CALL("AbstractingUnification::unifiers");

  // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
  // and therefore a constraint can be created between arguments
  if(topLevelCheck && t1.isTerm() && t2.isTerm() &&
     t1.term()->functor() != t2.term()->functor()){
    return SubstIterator::getEmpty();
  }

  bool unifies = unify(t1, index1, t2, index2, sub);

  if(!unifies){
    return SubstIterator::getEmpty();
  }

  if(!_fpi){
    return pvi(getSingletonIterator(sub));
  }

  bool success = fixedPointIteration(sub);
  return success ? pvi(getSingletonIterator(sub)) : SubstIterator::getEmpty();
}

SubstIterator AbstractingUnification::postprocess(RobSubstitution* sub, TermList t)
{
  CALL("AbstractingUnification::postprocess");
 
  if(!_fpi){
    return pvi(getSingletonIterator(sub));
  }

  bool success = fixedPointIteration(sub);
  return success ? pvi(getSingletonIterator(sub)) : SubstIterator::getEmpty();
}


#define DEBUG_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
bool AbstractingUnification::unify(TermSpec t1, TermSpec t2, bool& progress, RobSubstitution* sub)
{
  CALL("AbstractingUnification::unify");
  ASS_NEQ(_uwa._mode, Shell::Options::UnificationWithAbstraction::OFF) 
  DEBUG_UNIFY(1, ".unify(", t1, ",", t2, ")")
  progress = false;

  if(t1 == t2) {
    progress = true;
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<UnificationConstraint>> toDo;
    toDo->push(UnificationConstraint(t1.clone(), t2.clone()));

    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnificationConstraint>> encountered;

    Option<MismatchHandler::AbstractionResult> absRes;
    auto doAbstract = [&](auto& l, auto& r) -> bool
    { 
      absRes = _uwa.tryAbstract(sub, l, r);
      if (absRes) {
        DEBUG_UNIFY(2, "abstraction result: ", absRes)
      }
      return absRes.isSome();
    };

    auto pushTodo = [&](auto pair) {
        // we unify each subterm pair at most once, to avoid worst-case exponential runtimes
        // in order to safe memory we do ot do this for variables.
        // (Note by joe:  didn't make this decision, but just keeping the implemenntation 
        // working as before. i.e. as described in the paper "Comparing Unification 
        // Algorithms in First-Order Theorem Proving", by Krystof and Andrei)
        // TODO restore this branch?
        // if (pair.first.isVar() && isUnbound(pair.first.varSpec()) &&
        //     pair.second.isVar() && isUnbound(pair.second.varSpec())) {
        //   toDo.push(pair);
        // } else 
        if (!encountered->find(pair)) {
          encountered->insert(pair.clone());
          toDo->push(std::move(pair));
        }
    };


    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      auto& dt1 = x.lhs().deref(sub);
      auto& dt2 = x.rhs().deref(sub);
      DEBUG_UNIFY(2, "popped: ", dt1, " = ", dt2)
      if (dt1 == dt2) {
        progress = true;

      } else if(dt1.isVar() && !sub->occurs(dt1.varSpec(), dt2)) {
        progress = true;
        sub->bind(dt1.varSpec(), dt2.clone());

      } else if(dt2.isVar() && !sub->occurs(dt2.varSpec(), dt1)) {
        progress = true;
        sub->bind(dt2.varSpec(), dt1.clone());

      } else if(doAbstract(dt1, dt2)) {

        ASS(absRes);
        if (absRes->is<MismatchHandler::NeverEqual>()) {
          return false;

        } else {
          ASS(absRes->is<MismatchHandler::EqualIf>())
          auto& conditions = absRes->unwrap<MismatchHandler::EqualIf>();
          auto eq = [](UnificationConstraint& c, TermSpec const& lhs, TermSpec const& rhs) 
          { 
            return (c.lhs() == lhs && c.rhs() == rhs) 
                || (c.lhs() == rhs && c.rhs() == lhs); };
          if (progress 
              || conditions.constr().size() != 1 
              || conditions.unify().size() != 0
              || !eq(conditions.constr()[0], t1, t2)
              ) {
            progress = true;
          }
          for (auto& x : conditions.unify()) {
            pushTodo(std::move(x));
          }
          for (auto& x: conditions.constr()) {
            sub->pushConstraint(std::move(x));
          }
        }

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.functor() == dt2.functor()) {
        
        for (auto c : dt1.allArgs().zip(dt2.allArgs())) {
          pushTodo(UnificationConstraint(std::move(c.first), std::move(c.second)));
        }

      } else {
        return false;
      }

    }
    return true;
  };

  BacktrackData localBD;
  sub->bdRecord(localBD);
  bool success = impl();
  sub->bdDone();

  if(!success) {
    localBD.backtrack();
  } else {
    if(sub->bdIsRecording()) {
      sub->bdCommit(localBD);
    }
    localBD.drop();
  }

  DEBUG_UNIFY(1, *sub)
  return success;
}

}

}
