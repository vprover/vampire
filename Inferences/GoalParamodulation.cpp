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
 * @file GoalParamodulation.cpp
 * Implements class GoalParamodulation.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "GoalParamodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace std;

void GoalParamodulation::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);

  auto gp = salg->getOptions().goalParamodulation();
  _onlyUpwards = (gp == Options::GoalParamodulation::UP || gp == Options::GoalParamodulation::UP_LTR);
  _leftToRight = (gp == Options::GoalParamodulation::LTR || gp == Options::GoalParamodulation::UP_LTR);
  _chaining = salg->getOptions().goalParamodulationChaining();

  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(GOAL_PARAMODULATION_LHS_INDEX) );
  _subtermIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(GOAL_PARAMODULATION_SUBTERM_INDEX) );
}

void GoalParamodulation::detach()
{
  _lhsIndex = 0;
  _subtermIndex=0;
  _salg->getIndexManager()->release(GOAL_PARAMODULATION_LHS_INDEX);
  _salg->getIndexManager()->release(GOAL_PARAMODULATION_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

TermList replaceOccurrence(Term* t, Term* orig, TermList repl, const Position& pos)
{
  Stack<pair<Term*,unsigned>> todo;
  Term* curr = t;
  for (unsigned i = 0; i < pos.size(); i++) {
    auto p = pos[i];
    ASS_L(p,curr->arity());
    todo.push(make_pair(curr,p));

    auto next = curr->nthArgument(p);
    ASS(next->isTerm());
    curr = next->term();
  }
  ASS_EQ(orig,curr);
  TermList res = repl;

  while(todo.isNonEmpty()) {
    auto kv = todo.pop();
    TermStack args; 
    for (unsigned i = 0; i < kv.first->arity(); i++) {
      if (i == kv.second) {
        args.push(TermList(res));
      } else {
        args.push(*kv.first->nthArgument(i));
      }
    }
    res = TermList(Term::create(kv.first,args.begin()));
  }
  return res;
}

pair<Term*,Stack<unsigned>> PositionalNonVariableNonTypeIterator::next()
{
  auto kv = _stack.pop();
  TermList* ts;
  auto t = kv.first;

  for(unsigned i = t->numTypeArguments(); i < t->arity(); i++){
    ts = t->nthArgument(i);
    if (ts->isTerm()) {
      auto newPos = kv.second;
      newPos.push(i);
      _stack.push(make_pair(const_cast<Term*>(ts->term()),std::move(newPos)));
    }
  }
  return kv;
}

bool toTheLeftStrict(const Position& p1, const Position& p2)
{
  for (unsigned i = 0; i < p1.size(); i++) {
    if (p2.size() <= i) {
      return false;
    }
    if (p1[i] != p2[i]) {
      return p1[i] < p2[i];
    }
  }
  return false;
} 

vstring posToString(const Position& pos)
{
  vstring res;
  for (unsigned i = 0; i < pos.size(); i++) {
    res += Int::toString(pos[i]);
    if (i+1 < pos.size()) {
      res += '.';
    }
  }
  return res;
}

bool isInductionTerm(Term* t)
{
  // uncomment to use for general reasoning
  // return true;

  static DHMap<Term*,bool> cache;
  bool* ptr;
  if (!cache.getValuePtr(t,ptr,false)) {
    return *ptr;
  }

  if (!InductionHelper::isInductionTermFunctor(t->functor()) || !InductionHelper::isStructInductionTerm(t)) {
    return false;
  }
  *ptr = true;
  if (!t->ground()) {
    return true;
  }
  NonVariableNonTypeIterator nvi(t, true);
  while (nvi.hasNext()) {
    if (env.signature->getFunction(nvi.next()->functor())->skolem()) {
      return true;
    }
  }
  *ptr = false;
  return false;
}

void assertPositionIn(const Position& p, Term* t) {
  Term* curr = t;
  // cout << "assert pos " << *t << " " << posToString(p) << endl;
  for (const auto& i : p) {
    ASS_L(i,curr->arity());
    curr = curr->nthArgument(i)->term();
  }
}

inline bool hasTermToInductOn(TermList t) {
  if (t.isVar()) {
    return false;
  }
  NonVariableNonTypeIterator stit(t.term());
  while (stit.hasNext()) {
    auto st = stit.next();
    if (isInductionTerm(st)) {
      return true;
    }
  }
  return false;
}

VirtualIterator<pair<Term*,Position>> getPositions(TermList t, Term* st)
{
  if (t.isVar()) {
    return VirtualIterator<pair<Term*,Position>>::getEmpty();
  }
  return pvi(iterTraits(vi(new PositionalNonVariableNonTypeIterator(t.term())))
    .filter([st](pair<Term*,Position> arg) {
      return arg.first == st;
    }));
}

bool linear(TermList t)
{
  if (t.isVar()) {
    return true;
  }
  VariableIterator vit(t.term());
  DHSet<unsigned> vars;
  while (vit.hasNext()) {
    auto var = vit.next();
    if (!vars.insert(var.var())) {
      return false;
    }
  }
  return true;
}

bool shouldChain(Literal* lit, const Ordering& ord) {
  ASS(lit->isEquality() && lit->isPositive());
  auto comp = ord.getEqualityArgumentOrder(lit);
  if (comp == Ordering::INCOMPARABLE) {
    return false;
  }
  ASS_NEQ(comp,Ordering::EQUAL);
  auto side = lit->termArg((comp == Ordering::LESS || comp == Ordering::LESS_EQ) ? 1 : 0);
  return linear(side) && !hasTermToInductOn(side);
}

void getSkolems(Literal* lit, DHSet<unsigned>& skolems) {
  NonVariableNonTypeIterator it(lit);
  while (it.hasNext()) {
    auto trm = it.next();
    if (env.signature->getFunction(trm->functor())->skolem()) {
      skolems.insert(trm->functor());
    }
  }
}

VirtualIterator<TypedTermList> sideIterator(Literal* lit)
{
  auto res = VirtualIterator<TypedTermList>::getEmpty();
  for (unsigned i = 0; i <= 1; i++) {
    auto lhs = lit->termArg(i);
    auto rhs = lit->termArg(1-i);
    if (lhs.containsAllVariablesOf(rhs)) {
      res = pvi(getConcatenatedIterator(res, pvi(getSingletonIterator(TypedTermList(lhs,SortHelper::getEqualityArgumentSort(lit))))));
    }
  }
  return res;
}

ClauseIterator GoalParamodulation::generateClauses(Clause* premise)
{
  auto res = ClauseIterator::getEmpty();

  if (premise->length()!=1 || premise->goalParamodulationDepth()>=_salg->getOptions().maxGoalParamodulationDepth()) {
    return res;
  }

  auto lit = (*premise)[0];
  if (!lit->isEquality()) {
    return res;
  }

  // checking the skolems is pretty expensive, so we cache anything we can
  static DHMap<Clause*,bool> skolemsChecked;
  skolemsChecked.reset();

  static DHSet<unsigned> skolems;
  skolems.reset();
  getSkolems(lit,skolems);

  const auto& opt = _salg->getOptions();

  // forward
  if (lit->isNegative() && lit->ground()) {
    res = pvi(iterTraits(vi(new NonVariableNonTypeIterator(lit)))
      .unique()
      .flatMap([this](Term* t) {
        return pvi(pushPairIntoRightIterator(t,_lhsIndex->getGeneralizations(t, true)));
      })
      .filter([premise,&opt](pair<Term*,TermQueryResult> arg) {
        auto qr = arg.second;
        if (premise->goalParamodulationDepth()+qr.clause->goalParamodulationDepth()>=opt.maxGoalParamodulationDepth()) {
          return false;
        }
        if (SortHelper::getResultSort(arg.first) != SortHelper::getEqualityArgumentSort(qr.literal)) {
          return false;
        }
        // TODO this check with the Skolems is extremely expensive in some cases
        bool* skolemsOk;
        if (!skolemsChecked.getValuePtr(qr.clause, skolemsOk, false)) {
          return *skolemsOk;
        }
        auto rhs = EqHelper::getOtherEqualitySide(qr.literal,TermList(qr.term));
        if (rhs.isTerm()) {
          NonVariableNonTypeIterator it(rhs.term(),true);
          while (it.hasNext()) {
            auto trm = it.next();
            if (env.signature->getFunction(trm->functor())->skolem() && !skolems.contains(trm->functor())) {
              return false;
            }
          }
        }
        (*skolemsOk) = true;
        return true;
      })
      .flatMap([lit](pair<Term*,TermQueryResult> arg) {
        auto t0 = lit->termArg(0);
        auto t1 = lit->termArg(1);
        return pushPairIntoRightIterator(arg.second,
          pvi(getConcatenatedIterator(
            pvi(pushPairIntoRightIterator(t0.term(),getPositions(t0,arg.first))),
            pvi(pushPairIntoRightIterator(t1.term(),getPositions(t1,arg.first)))
          )));
      })
      .map([lit,premise,this](pair<TermQueryResult,pair<Term*,pair<Term*,Position>>> arg) -> Clause* {
        auto side = arg.second.first;
        auto lhsS = arg.second.second.first;
        auto pos = arg.second.second.second;
        auto qr = arg.first;
        return perform(premise,lit,side,lhsS,std::move(pos),qr.clause,qr.literal,qr.term,qr.substitution.ptr(),true);
      })
      .filter(NonzeroFn())
      .timeTraced("forward goal paramodulation"));
  }

  // backward
  if (lit->isPositive() && (!_chaining || !shouldChain(lit,_salg->getOrdering()))) {
    res = pvi(getConcatenatedIterator(res,pvi(iterTraits(sideIterator(lit))
      .flatMap([this](TypedTermList lhs) {
        return pvi(pushPairIntoRightIterator(lhs,_subtermIndex->getInstances(lhs,true)));
      })
      .filter([premise,lit,&opt](pair<TypedTermList,TermQueryResult> arg) {
        auto qr = arg.second;
        if (premise->goalParamodulationDepth()+qr.clause->goalParamodulationDepth()>=opt.maxGoalParamodulationDepth()) {
          return false;
        }
        if (SortHelper::getResultSort(qr.term.term()) != SortHelper::getEqualityArgumentSort(lit)) {
          return false;
        }
        bool* skolemsOk;
        if (!skolemsChecked.getValuePtr(qr.clause, skolemsOk, false) && !(*skolemsOk)) {
          return false;
        }
        if (!skolems.isEmpty()) {
          DHSet<unsigned> rwSkolems;
          getSkolems(qr.literal,rwSkolems);
          DHSet<unsigned>::Iterator it(skolems);
          while (it.hasNext()) {
            if (!rwSkolems.contains(it.next())) {
              return false;
            }
          }
        }
        (*skolemsOk) = true;
        return true;
      })
      .flatMap([](pair<TypedTermList,TermQueryResult> arg) {
        auto t = arg.second.term.term();
        auto t0 = arg.second.literal->termArg(0);
        auto t1 = arg.second.literal->termArg(1);
        return pushPairIntoRightIterator(arg,
          pvi(getConcatenatedIterator(
            pvi(pushPairIntoRightIterator(t0.term(),getPositions(t0,t))),
            pvi(pushPairIntoRightIterator(t1.term(),getPositions(t1,t)))
          )));
      })
      .map([lit,premise,this](pair<pair<TypedTermList,TermQueryResult>,pair<Term*,pair<Term*,Position>>> arg) -> Clause* {
        auto side = arg.second.first;
        auto pos = arg.second.second.second;
        auto qr = arg.first.second;
        auto eqLhs = arg.first.first;
        return perform(qr.clause, qr.literal, side, qr.term.term(), std::move(pos), premise, lit, eqLhs, qr.substitution.ptr(), false);
      })
      .filter(NonzeroFn())
      .timeTraced("backward goal paramodulation"))));
  }
  return res;
}

Clause* GoalParamodulation::perform(Clause* rwClause, Literal* rwLit, Term* rwSide, Term* rwTerm, Position&& pos,
  Clause* eqClause, Literal* eqLit, TermList eqLhs, ResultSubstitution* subst, bool eqIsResult)
{
  const auto& ord = _salg->getOrdering();

  auto rhs = EqHelper::getOtherEqualitySide(eqLit,TermList(eqLhs));
  auto rhsS = eqIsResult ? subst->applyToBoundResult(rhs) : subst->applyToBoundQuery(rhs);

  auto comp = ord.compare(TermList(rwTerm),rhsS);
  if (_onlyUpwards && comp != Ordering::Result::LESS) {
    return nullptr;
  }
  ASS_REP(!_chaining || !shouldChain(eqLit,ord), eqLit->toString());

  bool reversed = rwClause->reversed();
  bool switchedNew = false;
  if (_leftToRight) {
    // calculate positional stuff
    bool switched = rwClause->switched();
    const Position& sidePos = rwClause->position();

    // s = t, indexed 1 = 0
    if (reversed) {
      // rewriting 1
      if (TermList(rwSide) == rwLit->termArg(0)) {
        if (switched && toTheLeftStrict(pos,sidePos)) {
          return nullptr;
        }
        switchedNew = true;
      }
      // rewriting 0
      else {
        if (switched || toTheLeftStrict(pos,sidePos)) {
          return nullptr;
        }
      }
    }
    // s = t, indexed 0 = 1
    else {
      // rewriting 0
      if (TermList(rwSide) == rwLit->termArg(0)) {
        if (switched || toTheLeftStrict(pos,sidePos)) {
          return nullptr;
        }
      }
      // rewriting 1
      else {
        if (switched && toTheLeftStrict(pos,sidePos)) {
          return nullptr;
        }
        switchedNew = true;
      }
    }
  }

  auto tgtSide = replaceOccurrence(rwSide, rwTerm, rhsS, pos).term();
  auto other = EqHelper::getOtherEqualitySide(rwLit, TermList(rwSide));
  ASS_NEQ(tgtSide,other.term());
  auto resLit = Literal::createEquality(false, TermList(tgtSide), other, SortHelper::getEqualityArgumentSort(rwLit));

  Clause* res = new(1) Clause(1,
    GeneratingInference2(InferenceRule::GOAL_PARAMODULATION, rwClause, eqClause));
  (*res)[0]=resLit;
  res->setGoalParamodulationDepth(rwClause->goalParamodulationDepth()+eqClause->goalParamodulationDepth()+1);
  if (_leftToRight) {
    bool reversedNew = other == resLit->termArg(other == rwLit->termArg(0) ? 1 : 0);
    res->setPosInfo(reversed ^ reversedNew, switchedNew, std::move(pos));
  }

  env.statistics->goalParamodulations++;
  return res;
}

}