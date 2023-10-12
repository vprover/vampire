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
 * @file InductionRewriting.cpp
 * Implements class InductionRewriting.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionRewriting.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

// iterators and filters

TermList SingleOccurrenceReplacementIterator::Replacer::transformSubterm(TermList trm)
{
  if (trm.isVar() || _matchCount > _i) {
    return trm;
  }
  if (trm.term() == _o && _i == _matchCount++) {
    return _r;
  }
  return trm;
}

Term* SingleOccurrenceReplacementIterator::next()
{
  ASS(hasNext());
  if (_t == _o) {
    _iteration++;
    return _r.term();
  }
  Replacer sor(_o, _r, _iteration++);
  return sor.transform(_t);
}

// inference

void InductionRewriting::attach(SaturationAlgorithm* salg)
{
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(GOAL_PARAMODULATION_LHS_INDEX) );
  _subtermIndex=static_cast<TermIndex*>(
	  _salg->getIndexManager()->request(GOAL_PARAMODULATION_SUBTERM_INDEX) );
  // _induction->attach(salg);
}

void InductionRewriting::detach()
{
  // _induction->detach();
  // delete _induction;
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

bool toTheLeft(const Position& p1, const Position& p2)
{
  for (unsigned i = 0; i < p1.size(); i++) {
    if (p2.size() <= i) {
      return true;
    }
    if (p1[i] != p2[i]) {
      return p1[i] < p2[i];
    }
  }
  return true;
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

// void InductionRewriting::exploreTerm(Term* t, bool left)
// {
//   TIME_TRACE("InductionRewriting::exploreTerm");
//   auto& terms = left ? _leftTerms : _rightTerms;
//   terms.reset();
//   terms.insert(t);

//   Stack<pair<Term*,unsigned>> todo;
//   todo.push(make_pair(t,0));
//   const auto& ord = _salg->getOrdering();

//   while(todo.isNonEmpty()) {
//     auto kv = todo.pop();
//     auto curr = kv.first;
//     auto depth = kv.second;
//     if (depth >= MAX_DEPTH) {
//       continue;
//     }
//     // cout << "rewriting term " << *curr << endl;
//     iterTraits(vi(new NonVariableNonTypeIterator(curr,true)))
//       .unique()
//       .timeTraced("term iter")
//       .flatMap([this](Term* st) {
//         // cout << "st " << *st << endl;
//         return pvi(pushPairIntoRightIterator(st,_lhsIndex->getGeneralizations(st, true)));
//       })
//       .timeTraced("lhs index query")
//       .flatMap([curr,&ord](pair<Term*,TermQueryResult> arg) {
//         auto lhsS = arg.first;
//         auto qr = arg.second;
//         if (SortHelper::getResultSort(lhsS) != SortHelper::getEqualityArgumentSort(qr.literal)) {
//           return VirtualIterator<Term*>::getEmpty();
//         }
//         // cout << "eq " << *qr.literal << endl;
//         auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
//         auto rhsS = qr.substitution->applyToBoundResult(rhs);
//         if (ord.compare(TermList(lhsS),rhsS)!=Ordering::Result::LESS) {
//           return VirtualIterator<Term*>::getEmpty();
//         }
//         return pvi(vi(new SingleOccurrenceReplacementIterator(curr, lhsS, rhsS)));
//       })
//       .timeTraced("rewrite")
//       .forEach([&terms,&todo,depth](Term* res) {
//         if (terms.insert(res)) {
//           todo.push(make_pair(res,depth+1));
//         }
//       });
//   }
// }

Stack<Position> insertPosition(const Stack<Position>& ps, const Position& p)
{
  Stack<Position> res;
  for (const auto& q : ps) {
    bool diverged = false;
    for (unsigned i = 0; i < q.size(); i++) {
      if (p.size() <= i) {
        break;
      }
      if (p[i] != q[i]) {
        diverged = true;
        break;
      }
    }
    if (diverged) {
      res.push(q);
    }
  }
  res.push(p);
  return res;
}

void InductionRewriting::exploreTermLMIM(Term* t, bool left)
{
  TIME_TRACE("InductionRewriting::exploreTermLMIM");
  auto& terms = left ? _leftTerms : _rightTerms;
  terms.reset();
  Stack<Position> ps;
  ps.push(Position());
  terms.insert(t,std::move(ps));

  Stack<tuple<Term*,Stack<unsigned>,unsigned>> todo;
  todo.push(make_tuple(t,Stack<unsigned>(),0));
  const auto& ord = _salg->getOrdering();

  while(todo.isNonEmpty()) {
    auto tp = todo.pop();
    auto curr = get<0>(tp);
    auto pos = get<1>(tp);
    auto depth = get<2>(tp);
    if (depth >= env.options->maxGoalParamodulationDepth()) {
      continue;
    }
    // cout << "lmim rewriting term " << *curr << endl;
    iterTraits(vi(new PositionalNonVariableNonTypeIterator(curr)))
      .filter([pos](pair<Term*,Stack<unsigned>> arg) {
        return toTheLeft(pos, arg.second);
      })
      .flatMap([this](pair<Term*,Stack<unsigned>> arg) {
        // cout << "st " << *arg.first << " in " << posToString(arg.second) << endl;
        return pvi(pushPairIntoRightIterator(arg,_lhsIndex->getGeneralizations(arg.first, true)));
      })
      .map([curr,&ord](pair<pair<Term*,Stack<unsigned>>,TermQueryResult> arg) {
        auto lhsS = arg.first.first;
        auto pos = arg.first.second;
        auto qr = arg.second;
        if (SortHelper::getResultSort(lhsS) != SortHelper::getEqualityArgumentSort(qr.literal)) {
          return make_pair((Term*)nullptr,pos);
        }
        // cout << "eq " << *qr.literal << endl;
        auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        auto rhsS = qr.substitution->applyToBoundResult(rhs);
        if (ord.compare(TermList(lhsS),rhsS)!=Ordering::Result::LESS) {
          return make_pair((Term*)nullptr,pos);
        }
        return make_pair(replaceOccurrence(curr, lhsS, rhsS, pos).term(), pos);
      })
      .filter([](pair<Term*,Stack<unsigned>> res) {
        return res.first;
      })
      .forEach([&terms,&todo,depth,curr](pair<Term*,Stack<unsigned>> res) {
        if (!terms.find(res.first)) {
          // cout << "res " << *res.first << endl;
          todo.push(make_tuple(res.first,res.second,depth+1));
          terms.insert(res.first,insertPosition(terms.get(curr), res.second));
        }
      });
  }
}

Term* getTermAtPos(Term* t, const Position& p)
{
  Term* curr = t;
  for (const auto& i : p) {
    ASS_L(i,curr->arity());
    curr = curr->nthArgument(i)->term();
  }
  return curr;
}

bool isInductionTerm(Term* t)
{
  if (!InductionHelper::isInductionTermFunctor(t->functor())) {
    return false;
  }
  if (!InductionHelper::isStructInductionTerm(t)) {
    return false;
  }
  if (!t->ground()) {
    return true;
  }
  NonVariableNonTypeIterator nvi(t, true);
  while (nvi.hasNext()) {
    if (env.signature->getFunction(nvi.next()->functor())->skolem()) return true;
  }
  return false;
}

// void getTermsToInductOn(Term* t, const Stack<Position>& ps, DHSet<Term*>& indTerms)
// {
//   indTerms.reset();
//   ASS(ps.isNonEmpty());
//   auto st = getTermAtPos(t,ps[0]);
//   NonVariableNonTypeIterator nvi(st,true);
//   while (nvi.hasNext()) {
//     auto stt = nvi.next();
//     if (isInductionTerm(stt)) {
//       indTerms.insert(stt);
//     }
//   }
//   if (indTerms.isEmpty()) {
//     return;
//   }
//   for (unsigned i = 1; i < ps.size(); i++) {
//     DHSet<Term*> inner;
//     auto st = getTermAtPos(t,ps[i]);
//     NonVariableNonTypeIterator nvi(st,true);
//     while (nvi.hasNext()) {
//       auto stt = nvi.next();
//       if (isInductionTerm(stt) && indTerms.contains(stt)) {
//         inner.insert(stt);
//       }
//     }
//     DHSet<Term*>::DelIterator it(indTerms);
//     while (it.hasNext()) {
//       if (!inner.contains(it.next())) {
//         it.del();
//       }
//     }
//   }
// }

Position getRightmostPosition(const Stack<pair<Position,bool>>& ps, bool left) {
  Position curr;
  for (auto& kv : ps) {
    if (kv.second != left) {
      continue;
    }
    if (toTheLeft(curr,kv.first)) {
      curr = kv.first;
    }
  }
  return curr;
}

void assertPositionIn(const Position& p, Term* t) {
  Term* curr = t;
  // cout << "assert pos " << *t << " " << posToString(p) << endl;
  for (const auto& i : p) {
    ASS_L(i,curr->arity());
    curr = curr->nthArgument(i)->term();
  }
}

inline bool hasTermToInductOn(Term* t) {
  NonVariableNonTypeIterator stit(t);
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

bool linear(Term* t)
{
  SubtermIterator stit(t);
  DHSet<unsigned> vars;
  while (stit.hasNext()) {
    auto st = stit.next();
    if (st.isVar() && !vars.insert(st.var())) {
      return false;
    }
  }
  return true;
}

bool shouldChain (Term* lhs) {
  return linear(lhs) && !hasTermToInductOn(lhs);
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

VirtualIterator<TypedTermList> lhsIterator(Literal* lit)
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

template<class TermListIter>
auto withEqualitySort(Literal* eq, TermListIter iter)
{ return pvi(iterTraits(std::move(iter))
    .map([eq](TermList t) { return TypedTermList(t, SortHelper::getEqualityArgumentSort(eq)); })); }

VirtualIterator<TypedTermList> orderedLhsIterator(Literal* lit, const Ordering& ord, bool reverse)
{
  ASS(lit->isEquality() && lit->isPositive());

  TermList t0=*lit->nthArgument(0);
  TermList t1=*lit->nthArgument(1);
  switch(ord.getEqualityArgumentOrder(lit))
  {
  case Ordering::INCOMPARABLE:
    return withEqualitySort(lit, getConcatenatedIterator(getSingletonIterator(t0),getSingletonIterator(t1)) );
  case Ordering::GREATER:
  case Ordering::GREATER_EQ:
    return withEqualitySort(lit, getSingletonIterator(reverse ? t1 : t0) );
  case Ordering::LESS:
  case Ordering::LESS_EQ:
    return withEqualitySort(lit, getSingletonIterator(reverse ? t0 : t1) );
  //there should be no equality literals of equal terms
  case Ordering::EQUAL:
    break;
  }
  ASSERTION_VIOLATION;
}

ClauseIterator InductionRewriting::generateClauses(Clause* premise)
{
  auto res = ClauseIterator::getEmpty();

  if (premise->length()!=1 || premise->remDepth()>=_salg->getOptions().maxGoalParamodulationDepth()) {
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
      .flatMap([this](Term* t) {
        return pvi(pushPairIntoRightIterator(t,_lhsIndex->getGeneralizations(t, true)));
      })
      .filter([premise,&opt](pair<Term*,TermQueryResult> arg) {
        auto qr = arg.second;
        if (premise->remDepth()+qr.clause->remDepth()>=opt.maxGoalParamodulationDepth()) {
          return false;
        }
        if (SortHelper::getResultSort(arg.first) != SortHelper::getEqualityArgumentSort(qr.literal)) {
          return false;
        }
        bool* skolemsOk;
        if (!skolemsChecked.getValuePtr(qr.clause, skolemsOk, false) && !(*skolemsOk)) {
          return false;
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
  if (lit->isPositive()) {
    res = pvi(getConcatenatedIterator(res,pvi(iterTraits(lhsIterator(lit))
      .flatMap([this](TypedTermList lhs) {
        return pvi(pushPairIntoRightIterator(lhs,_subtermIndex->getInstances(lhs,true)));
      })
      .filter([premise,lit,&opt](pair<TypedTermList,TermQueryResult> arg) {
        auto qr = arg.second;
        if (premise->remDepth()+qr.clause->remDepth()>=opt.maxGoalParamodulationDepth()) {
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

inline bool onlyUpwards(Options::GoalParamodulation gp) {
  return gp == Options::GoalParamodulation::UP || gp == Options::GoalParamodulation::UP_LMIM;
}

inline bool lmim(Options::GoalParamodulation gp) {
  return gp == Options::GoalParamodulation::LMIM || gp == Options::GoalParamodulation::UP_LMIM;
}

Clause* InductionRewriting::perform(Clause* rwClause, Literal* rwLit, Term* rwSide, Term* rwTerm, Position&& pos,
  Clause* eqClause, Literal* eqLit, TermList eqLhs, ResultSubstitution* subst, bool eqIsResult)
{
  const auto& opt = _salg->getOptions();
  const auto& ord = _salg->getOrdering();

  auto rhs = EqHelper::getOtherEqualitySide(eqLit,TermList(eqLhs));
  auto rhsS = eqIsResult ? subst->applyToBoundResult(rhs) : subst->applyToBoundQuery(rhs);

  auto comp = ord.compare(TermList(rwTerm),rhsS);
  if (onlyUpwards(opt.goalParamodulation()) && comp != Ordering::Result::LESS) {
    return nullptr;
  }
  if (comp == Ordering::Result::LESS && opt.goalParamodulationChaining() && shouldChain(rhs.term())) {
    return nullptr;
  }

  bool reversed = rwClause->reversed();
  bool switchedNew = false;
  if (lmim(opt.goalParamodulation())) {
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
    GeneratingInference2(InferenceRule::FORWARD_REMODULATION, rwClause, eqClause));
  (*res)[0]=resLit;
  res->setRemDepth(rwClause->remDepth()+eqClause->remDepth()+1);
  if (lmim(opt.goalParamodulation())) {
    bool reversedNew = other == resLit->termArg(other == rwLit->termArg(0) ? 1 : 0);
    res->setPosInfo(reversed ^ reversedNew, switchedNew, std::move(pos));
  }

  env.statistics->goalParamodulations++;
  return res;
}

}