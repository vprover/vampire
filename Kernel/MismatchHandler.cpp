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
  Recycled<TermStack> _todo;
  RobSubstitutionTL const* _subs;
public:
  AcIter(unsigned function, TermList t, RobSubstitutionTL const* subs) : _function(function), _todo(), _subs(subs) 
  { _todo->push(t); }

  DECL_ELEMENT_TYPE(TermList);

  bool hasNext() const { return !_todo->isEmpty(); }

  TermList next() {
    ASS(!_todo->isEmpty());
    auto t = _todo->pop();
    auto dt = _subs->derefBound(t);
    while (dt.isTerm() && dt.term()->functor() == _function) {
      ASS_EQ(dt.term()->arity(), 2);
      _todo->push(dt.term()->termArg(1));
      t = dt.term()->termArg(0);
      dt = _subs->derefBound(t);
    }
    return dt;
  }
};

// auto acIter(unsigned f, TermSpec t)
// { return iterTraits(AcIter(f, t)); }

bool MismatchHandler::canAbstract(TermList const& t1, TermList const& t2) const 
{
  
  auto isNumeral = [](TermList t){
    ASS(t.isTerm());
    return env.signature->getFunction(t.term()->functor())->interpretedNumber();
  };
 
  if(!(t1.isTerm() && t2.isTerm())) return false;
  if(t1.term()->isSort() || t2.term()->isSort()) return false;

  bool t1Interp = isInterpreted(t1.term()->functor());
  bool t2Interp = isInterpreted(t2.term()->functor());
  bool bothNumbers = isNumeral(t1) && isNumeral(t2);

  switch(_mode) {
    case Shell::Options::UnificationWithAbstraction::INTERP_ONLY:
      return (t1Interp && t2Interp && !bothNumbers);
    case Shell::Options::UnificationWithAbstraction::ONE_INTERP:
      return !bothNumbers && (t1Interp || t2Interp);
      break;
    case Shell::Options::UnificationWithAbstraction::CONSTANT:
      return !bothNumbers && (t2Interp || t2Interp)
            && (t1Interp || t1.term()->numTermArguments())
            && (t2Interp || t2.term()->numTermArguments());
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

Option<MismatchHandler::AbstractionResult> MismatchHandler::tryAbstract(RobSubstitutionTL* sub, TermList const& t1, TermList const& t2) const
{
  CALL("MismatchHandler::checkUWA");
  using Uwa = Shell::Options::UnificationWithAbstraction;
  ASS(_mode != Uwa::OFF)


  // TODO add parameter instead of reading from options
  if (_mode == Uwa::AC1 || _mode == Uwa::AC2) {
    if (!(t1.isTerm() && theory->isInterpretedFunction(t1.term()->functor(), IntTraits::addI))
     || !(t2.isTerm() && theory->isInterpretedFunction(t2.term()->functor(), IntTraits::addI))) {
      return Option<AbstractionResult>();
    }
    auto a1 = iterTraits(AcIter(IntTraits::addF(), t1, sub)).template collect<Stack>();
    auto a2 = iterTraits(AcIter(IntTraits::addF(), t2, sub)).template collect<Stack>();
    // TODO not sure that the below works as desired AYB
    auto less = [&](TermList const& lhs, TermList const& rhs) { return lhs < rhs; };
    a1.sort(less);
    a2.sort(less);

    Recycled<TermStack> diff1_;
    Recycled<TermStack> diff2_;
    auto& diff1 = *diff1_;
    auto& diff2 = *diff2_;
    diff1.moveFromIterator(iterSortedDiff(arrayIter(a1), arrayIter(a2)).map([](auto& x) -> TermList { return x; }));
    diff2.moveFromIterator(iterSortedDiff(arrayIter(a2), arrayIter(a1)).map([](auto& x) -> TermList { return x; }));
    auto sum = [](auto& diff) {
        return arrayIter(diff)
          .map([](auto& x) { return x; })
          .fold([](auto l, auto r) 
            { 
              TermList args[] = {l, r};
              return TermList(Term::createNonShared(IntTraits::addF(), 2, args)); 
            }) //create non-shared? 
          .unwrap(); };
    auto diffConstr = [&]() 
    { return UnifConstraint(sum(diff1), sum(diff2)); };

    auto functors = [](auto& diff) 
    { return arrayIter(diff).map([](auto& f) { return f.term()->functor(); }); };

    if (diff1.size() == 0 && diff2.size() == 0) {
      return some(AbstractionResult(EqualIf()));

    } else if (( diff1.size() == 0 && diff2.size() != 0 )
            || ( diff2.size() == 0 && diff1.size() != 0 ) ) {
      return some(AbstractionResult(NeverEqual{}));

    } else if (_mode == Uwa::AC2 && diff1.size() == 1 && diff1[0].isVar()) {
      return some(AbstractionResult(EqualIf().unify(UnifConstraint(diff1[0], sum(diff2)))));

    } else if (_mode == Uwa::AC2 && diff2.size() == 1 && diff2[0].isVar()) {
      return some(AbstractionResult(EqualIf().unify(UnifConstraint(diff2[0], sum(diff1)))));

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
        return AbstractionResult(EqualIf().constr(UnifConstraint(t1, t2)));
    });
  }
}

namespace UnificationAlgorithms {


bool AbstractingUnification::fixedPointIteration(RobSubstitutionTL* sub)
{
  CALL("AbstractingUnification::fixedPointIteration");
  Recycled<Stack<UnificationConstraint<TermList,VarBank>>> todo;
  while (!sub->emptyConstraints()) { 
    todo->push(sub->popConstraint());
  }

  DEBUG_FINALIZE(1, "finalizing: ", todo)
  while (!todo->isEmpty()) {
    auto c = todo->pop();
    DEBUG_FINALIZE(2, "popped: ", c);
    bool progress;
    auto res = unify(c.lhs(), c.rhs(), progress, sub);
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

bool AbstractingUnification::unify(TermList term1, TermList term2, RobSubstitutionTL* sub)
{
  ASS(_uwa._mode != Shell::Options::UnificationWithAbstraction::OFF); 

  bool progress;
  return unify(term1, term2, progress, sub);
}

SubstIterator AbstractingUnification::unifiers(TermList t1, TermList t2, RobSubstitutionTL* sub, bool topLevelCheck)
{
  CALL("AbstractingUnification::unifiers");

  // We only care about non-trivial constraints where the top-sybmol of the two literals are the same
  // and therefore a constraint can be created between arguments
  if(topLevelCheck && t1.isTerm() && t2.isTerm() &&
     t1.term()->functor() != t2.term()->functor()){
    return SubstIterator::getEmpty();
  }

  bool unifies = unify(t1, t2, sub);

  if(!unifies){
    return SubstIterator::getEmpty();
  }

  if(!_fpi){
    return pvi(getSingletonIterator(sub));
  }

  bool success = fixedPointIteration(sub);
  return success ? pvi(getSingletonIterator(sub)) : SubstIterator::getEmpty();
}

SubstIterator AbstractingUnification::postprocess(RobSubstitutionTL* sub, TermList t, TermList sort)
{
  CALL("AbstractingUnification::postprocess");
 
  if(!_fpi){
    return pvi(getSingletonIterator(sub));
  }

  bool success = fixedPointIteration(sub);
  return success ? pvi(getSingletonIterator(sub)) : SubstIterator::getEmpty();
}


#define DEBUG_UNIFY(LVL, ...) if (LVL <= 0) DBG(__VA_ARGS__)
bool AbstractingUnification::unify(TermList t1, TermList t2, bool& progress, RobSubstitutionTL* sub)
{
  CALL("AbstractingUnification::unify");
  ASS_NEQ(_uwa._mode, Shell::Options::UnificationWithAbstraction::OFF) 
  DEBUG_UNIFY(1, ".unify(", t1, ",", t2, ")")
  progress = false;

  if(sub->sameTermContent(t1,t2)) {
    progress = true;
    return true;
  }

  auto impl = [&]() -> bool {

    Recycled<Stack<UnificationConstraint<TermList,VarBank>>> toDo;
    toDo->push(UnificationConstraint<TermList,VarBank>(t1, t2));

    // Save encountered unification pairs to avoid
    // recomputing their unification
    Recycled<DHSet<UnificationConstraint<TermList,VarBank>>> encountered;

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
          encountered->insert(pair);
          toDo->push(pair);
        }
    };


    while (toDo->isNonEmpty()) {
      auto x = toDo->pop();
      TermList dt1 = sub->derefBound(x.lhs());
      TermList dt2 = sub->derefBound(x.rhs());

      DEBUG_UNIFY(2, "popped: ", dt1, " = ", dt2)
      if (sub->sameTermContent(dt1, dt2)) {
        progress = true;

      } else if(dt1.isVar() && !sub->occurs(dt1, dt2)) {
        progress = true;
        sub->bind(dt1, dt2);

      } else if(dt2.isVar() && !sub->occurs(dt2, dt1)) {
        progress = true;
        sub->bind(dt2, dt1);

      } else if(doAbstract(dt1, dt2)) {

        ASS(absRes);
        if (absRes->is<MismatchHandler::NeverEqual>()) {
          return false;

        } else {
          ASS(absRes->is<MismatchHandler::EqualIf>())
          auto& conditions = absRes->unwrap<MismatchHandler::EqualIf>();
          auto eq = [](UnificationConstraint<TermList,VarBank>& c, TermList const& lhs, TermList const& rhs) 
          { 
            // equals instead of == because some of the terms could be non-shared
            return (TermList::equals(c.lhs(),lhs) && TermList::equals(c.rhs(),rhs)) 
                || (TermList::equals(c.lhs(),rhs) && TermList::equals(c.rhs(),lhs)); };
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

      } else if(dt1.isTerm() && dt2.isTerm() && dt1.term()->functor() == dt2.term()->functor()) {
        
        for (unsigned i = 0; i < dt1.term()->arity(); i++) {
          pushTodo(UnificationConstraint<TermList,VarBank>(dt1.nthArg(i), dt2.nthArg(i)));
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
