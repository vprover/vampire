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
 * @file GoalRewriting.cpp
 * Implements class GoalRewriting.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "GoalRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace std;

#define INDUCTION_MODE

void GoalRewriting::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);

  auto gp = salg->getOptions().goalRewriting();
  _onlyUpwards = (gp == Options::GoalRewriting::UP || gp == Options::GoalRewriting::UP_LTR);
  _leftToRight = (gp == Options::GoalRewriting::LTR || gp == Options::GoalRewriting::UP_LTR);
  _chaining = salg->getOptions().goalRewritingChaining();

  _lhsIndex=static_cast<TermIndex<TermLiteralClause>*>(
	  _salg->getIndexManager()->request(GOAL_REWRITING_LHS_INDEX) );
  _subtermIndex=static_cast<TermIndex<TermLiteralClause>*>(
	  _salg->getIndexManager()->request(GOAL_REWRITING_SUBTERM_INDEX) );
}

void GoalRewriting::detach()
{
  _lhsIndex = 0;
  _subtermIndex=0;
  _salg->getIndexManager()->release(GOAL_REWRITING_LHS_INDEX);
  _salg->getIndexManager()->release(GOAL_REWRITING_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

TermList replaceOccurrence(Term* t, const Term* orig, TermList repl, const Position& pos)
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

std::string posToString(const Position& pos)
{
  std::string res;
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
#ifdef INDUCTION_MODE
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
#else
  return true;
#endif
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

VirtualIterator<pair<Term*,Position>> getPositions(TermList t, const Term* st)
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
  auto side = lit->termArg(comp == Ordering::LESS ? 1 : 0);
  return linear(side) && !hasTermToInductOn(side);
}

#ifdef INDUCTION_MODE
DHSet<unsigned>* getSkolems(Literal* lit) {
  TIME_TRACE("getSkolems");
  // checking the skolems is pretty expensive, so we cache them per literal
  static DHMap<Literal*,DHSet<unsigned>> skolemCache;
  DHSet<unsigned>* ptr;
  if (!skolemCache.getValuePtr(lit, ptr)) {
    return ptr;
  }
  NonVariableNonTypeIterator it(lit);
  while (it.hasNext()) {
    auto trm = it.next();
    if (env.signature->getFunction(trm->functor())->skolem()) {
      ptr->insert(trm->functor());
    }
  }
  return ptr;
}
#endif

VirtualIterator<TypedTermList> sideIterator(Literal* lit)
{
  auto res = VirtualIterator<TypedTermList>::getEmpty();
  for (unsigned i = 0; i <= 1; i++) {
    auto lhs = lit->termArg(i);
    auto rhs = lit->termArg(1-i);
    if (lhs.containsAllVariablesOf(rhs)) {
      res = pvi(concatIters(res, pvi(getSingletonIterator(TypedTermList(lhs,SortHelper::getEqualityArgumentSort(lit))))));
    }
  }
  return res;
}

VirtualIterator<Term*> termIterator(Literal* lit, Clause* cl, bool leftToRight) {
  ASS(lit->isEquality() && lit->isNegative() && lit->ground());
  if (!leftToRight) {
    return vi(new NonVariableNonTypeIterator(lit));
  }
  bool reversed = cl->reversed();
  bool switched = cl->switched();
  const Position& pos = cl->position();
  TermList currSide = lit->termArg((reversed ^ switched) ? 1 : 0);
  TermList other = lit->termArg((reversed ^ switched) ? 0 : 1);
  if (pos.isEmpty() && !switched) {
    return vi(new NonVariableNonTypeIterator(lit));
  }
  auto res = VirtualIterator<Term*>::getEmpty();
  Term* curr = currSide.term();
  for (const auto& i : pos) {
    // add args to the right of index
    for (unsigned j = i+1; j < curr->arity(); j++) {
      auto arg = *curr->nthArgument(j);
      res = pvi(concatIters(res, vi(new NonVariableNonTypeIterator(arg.term(),true))));
    }
    // add term itself
    res = pvi(concatIters(res, getSingletonIterator(curr)));
    curr = curr->nthArgument(i)->term();
  }
  // add last term and all its subterms
  res = pvi(concatIters(res, vi(new NonVariableNonTypeIterator(curr,true))));
  if (!switched) {
    res = pvi(concatIters(res, vi(new NonVariableNonTypeIterator(other.term(),true))));
  }
  return res;
}

ClauseIterator GoalRewriting::generateClauses(Clause* premise)
{
  auto res = ClauseIterator::getEmpty();

  if (premise->length()!=1 || premise->goalRewritingDepth()>=_salg->getOptions().maxGoalRewritingDepth()) {
    return res;
  }

  auto lit = (*premise)[0];
  if (!lit->isEquality()) {
    return res;
  }

  const auto& opt = _salg->getOptions();

  // forward
  if (lit->isNegative() && lit->ground()) {
    res = pvi(iterTraits(termIterator(lit,premise,_leftToRight))
      .unique()
      .flatMap([this](Term* t) {
        return pvi(pushPairIntoRightIterator(t,_lhsIndex->getGeneralizations(t, true)));
      })
      .filter([premise,&opt,lit](pair<Term*,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto qr = arg.second;
        if (premise->goalRewritingDepth()+qr.data->clause->goalRewritingDepth()>=opt.maxGoalRewritingDepth()) {
          return false;
        }
        if (SortHelper::getResultSort(arg.first) != SortHelper::getEqualityArgumentSort(qr.data->literal)) {
          return false;
        }
#ifdef INDUCTION_MODE
        DHSet<unsigned> sks;
        sks.loadFromIterator(DHSet<unsigned>::Iterator(*getSkolems(lit)));
        DHSet<unsigned>::Iterator skIt(*getSkolems(qr.data->literal));
        while (skIt.hasNext()) {
          if (!sks.contains(skIt.next())) {
            return false;
          }
        }
#endif
        return true;
      })
      .flatMap([lit](pair<Term*,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto t0 = lit->termArg(0);
        auto t1 = lit->termArg(1);
        return pushPairIntoRightIterator(arg.second,
          pvi(concatIters(
            pvi(pushPairIntoRightIterator(t0.term(),getPositions(t0,arg.first))),
            pvi(pushPairIntoRightIterator(t1.term(),getPositions(t1,arg.first)))
          )));
      })
      .map([lit,premise,this](pair<QueryRes<ResultSubstitutionSP, TermLiteralClause>,pair<Term*,pair<Term*,Position>>> arg) -> Clause* {
        auto side = arg.second.first;
        auto lhsS = arg.second.second.first;
        auto pos = arg.second.second.second;
        auto qr = arg.first;
        return perform(premise,lit,side,lhsS,std::move(pos),qr.data->clause,qr.data->literal,qr.data->term,qr.unifier.ptr(),true);
      })
      .filter(NonzeroFn()));
  }

  // backward
  if (lit->isPositive() && (!_chaining || !shouldChain(lit,_salg->getOrdering()))) {
    res = pvi(concatIters(res,pvi(iterTraits(sideIterator(lit))
      .flatMap([this](TypedTermList lhs) {
        return pvi(pushPairIntoRightIterator(lhs,_subtermIndex->getInstances(lhs,true)));
      })
      .filter([premise,lit,&opt](pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto qr = arg.second;
        if (premise->goalRewritingDepth()+qr.data->clause->goalRewritingDepth()>=opt.maxGoalRewritingDepth()) {
          return false;
        }
        if (SortHelper::getResultSort(qr.data->term.term()) != SortHelper::getEqualityArgumentSort(lit)) {
          return false;
        }
#ifdef INDUCTION_MODE
        DHSet<unsigned> sks;
        sks.loadFromIterator(DHSet<unsigned>::Iterator(*getSkolems(lit)));
        if (sks.isEmpty()) {
          return true;
        }
        auto skPtrOther = getSkolems(qr.data->literal);
        DHSet<unsigned>::Iterator skIt(sks);
        while (skIt.hasNext()) {
          if (!skPtrOther->contains(skIt.next())) {
            return false;
          }
        }
#endif
        return true;
      })
      .flatMap([](pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>> arg) {
        auto t = arg.second.data->term.term();
        auto t0 = arg.second.data->literal->termArg(0);
        auto t1 = arg.second.data->literal->termArg(1);
        return pushPairIntoRightIterator(arg,
          pvi(concatIters(
            pvi(pushPairIntoRightIterator(t0.term(),getPositions(t0,t))),
            pvi(pushPairIntoRightIterator(t1.term(),getPositions(t1,t)))
          )));
      })
      .map([lit,premise,this](pair<pair<TypedTermList,QueryRes<ResultSubstitutionSP, TermLiteralClause>>,pair<Term*,pair<Term*,Position>>> arg) -> Clause* {
        auto side = arg.second.first;
        auto pos = arg.second.second.second;
        auto qr = arg.first.second;
        auto eqLhs = arg.first.first;
        return perform(qr.data->clause, qr.data->literal, side, qr.data->term.term(), std::move(pos), premise, lit, eqLhs, qr.unifier.ptr(), false);
      })
      .filter(NonzeroFn()))));
  }
  auto resTT = TIME_TRACE_ITER("goal rewriting", res);
  return pvi(resTT);
}

Clause* GoalRewriting::perform(Clause* rwClause, Literal* rwLit, Term* rwSide, const Term* rwTerm, Position&& pos,
  Clause* eqClause, Literal* eqLit, TermList eqLhs, ResultSubstitution* subst, bool eqIsResult)
{
  const auto& ord = _salg->getOrdering();

  auto rhs = EqHelper::getOtherEqualitySide(eqLit,TermList(eqLhs));
  auto rhsS = eqIsResult ? subst->applyToBoundResult(rhs) : subst->applyToBoundQuery(rhs);

  if (_onlyUpwards && ord.compare(TermList(const_cast<Term*>(rwTerm)),rhsS) != Ordering::Result::LESS) {
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
  LiteralStack resLits;
  resLits.push(Literal::createEquality(false, TermList(tgtSide), other, SortHelper::getEqualityArgumentSort(rwLit)));

  Clause* res = Clause::fromStack(resLits, GeneratingInference2(InferenceRule::GOAL_REWRITING, rwClause, eqClause));
  res->setGoalRewritingDepth(rwClause->goalRewritingDepth()+eqClause->goalRewritingDepth()+1);
  if (_leftToRight) {
    bool reversedNew = other == resLits[0]->termArg(other == rwLit->termArg(0) ? 1 : 0);
    res->setPosInfo(reversed ^ reversedNew, switchedNew, std::move(pos));
  }

  env.statistics->goalRewritings++;
  return res;
}

}