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
 * @file ReducibilityChecker.cpp
 * Implements class ReducibilityChecker.
 */

#include "Lib/Environment.hpp"
#include "Lib/BitUtils.hpp"

#include "Shell/Statistics.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/VarOrder.hpp"
#include "Kernel/SubstHelper.hpp"

#include "Indexing/ResultSubstitution.hpp"

#include "ReducibilityChecker.hpp"
#include "ForwardGroundJoinability.hpp"

using namespace std;
using namespace Indexing;

#define LOGGING 0

#if LOGGING
#define LOG1(s,arg) s << arg << endl;
#define LOG2(s,a1,a2) s << a1 << a2 << endl;
#define LOG3(s,a1,a2,a3) s << a1 << a2 << a3 << endl;
#define LOG4(s,a1,a2,a3,a4) s << a1 << a2 << a3 << a4 << endl;
#else
#define LOG1(s,arg)
#define LOG2(s,a1,a2)
#define LOG3(s,a1,a2,a3)
#define LOG4(s,a1,a2,a3,a4)
#endif

namespace Inferences {

inline bool cannotBeGreater(Term* t1, Term* t2) {
  return t1->numVarOccs() < t2->numVarOccs() || (~t1->varmap() & t2->varmap()) || t1->weight() < t2->weight();
}

void getLHSIterator(Literal* lit, ResultSubstitution* subst, bool result, const Ordering& ord, Stack<pair<TermList,TermList>>& sides)
{
  if (!lit->isEquality()) {
    sides.push(make_pair(TermList(lit),TermList(subst->apply(lit,result))));
    return;
  }

  TermList t0=*lit->nthArgument(0);
  TermList t1=*lit->nthArgument(1);
  switch(ord.getEqualityArgumentOrder(lit))
  {
  case Ordering::INCOMPARABLE: {
    auto t0S = subst->apply(t0,result);
    auto t1S = subst->apply(t1,result);
    switch(ord.compare(t0S,t1S)) {
      case Ordering::INCOMPARABLE: {
        sides.push(make_pair(t0,t0S));
        sides.push(make_pair(t1,t1S));
        break;
      }
      case Ordering::GREATER:
      case Ordering::GREATER_EQ:
        sides.push(make_pair(t0,t0S));
        break;
      case Ordering::LESS:
      case Ordering::LESS_EQ:
        sides.push(make_pair(t1,t1S));
        break;
      //there should be no equality literals of equal terms
      case Ordering::EQUAL:
        ASSERTION_VIOLATION;
    }
    break;
  }
  case Ordering::GREATER:
  case Ordering::GREATER_EQ:
    sides.push(make_pair(t0,subst->apply(t0,result)));
    break;
  case Ordering::LESS:
  case Ordering::LESS_EQ:
    sides.push(make_pair(t1,subst->apply(t1,result)));
    break;
  //there should be no equality literals of equal terms
  case Ordering::EQUAL:
    ASSERTION_VIOLATION;
  }
}

ReducibilityChecker::ReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt)
: _index(index), _ord(ord), _opt(opt) {}

bool ReducibilityChecker::check(Clause* rwClause, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult)
{
  TIME_TRACE("ReducibilityChecker::check");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  Stack<Literal*> lits;
  for (unsigned i = 0; i < rwClause->numSelected(); i++) {
    lits.push(subst->apply((*rwClause)[i],!eqIsResult));
  }
  for (unsigned i = 0; i < eqClause->numSelected(); i++) {
    lits.push(subst->apply((*eqClause)[i],eqIsResult));
  }
  auto rwTermS = subst->apply(eqLHS,eqIsResult).term();
  auto tgtTermS = subst->apply(EqHelper::getOtherEqualitySide(eqLit,eqLHS),eqIsResult);
  switch (_opt.reducibilityCheck()) {
    case Options::ReducibilityCheck::SMALLER: {
      vstringstream exp;
      return checkSmallerSanity(lits, rwTermS, &tgtTermS, exp);
    }
    case Options::ReducibilityCheck::SMALLER_GROUND: {
      vstringstream exp;
      return checkSmaller(lits, rwTermS, &tgtTermS, eqClause, eqLit, eqLHS, subst, eqIsResult, exp);
    }
    default:
      return false;
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::checkSmaller(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult, vstringstream& exp)
{
  Stack<Term*> toplevelTerms;
  for (const auto& lit : lits) {
    if (!lit->isEquality()) {
      toplevelTerms.push(lit);
    } else {
      auto comp = _ord.getEqualityArgumentOrder(lit);
      auto t0 = lit->termArg(0);
      auto t1 = lit->termArg(1);
      switch(comp) {
        case Ordering::INCOMPARABLE:
          if (t0.isTerm()) { toplevelTerms.push(t0.term()); }
          if (t1.isTerm()) { toplevelTerms.push(t1.term()); }
          break;
        case Ordering::GREATER:
        case Ordering::GREATER_EQ:
          ASS(t0.isTerm());
          toplevelTerms.push(t0.term());
          break;
        case Ordering::LESS:
        case Ordering::LESS_EQ:
          ASS(t1.isTerm());
          toplevelTerms.push(t1.term());
          break;
        case Ordering::EQUAL:
          ASSERTION_VIOLATION;
      }
    }
  }
  DHSet<Term*> attemptedOuter;

  Stack<VarOrder> todo;
  todo.push(VarOrder());
  while (todo.isNonEmpty()) {
    auto vo = todo.pop();
    VarOrder::EqApplicator voApp(vo);
    auto rwTermSS = SubstHelper::apply(rwTermS, voApp);
    TermList tgtTermSS = SubstHelper::apply(*tgtTermS, voApp);
    if (tgtTermSS == TermList(rwTermSS) || _ord.isGreater(tgtTermSS,TermList(rwTermSS),vo)) {
      // the superposition itself is redundant, skip this order
      continue;
    }

    VarOrder ext = vo;
    if (_ord.makeGreater(tgtTermSS,TermList(rwTermSS),ext)) {
      auto vos = ForwardGroundJoinability::order_diff(vo,ext);
      for (auto&& evo : vos) {
        todo.push(std::move(evo));
      }
      continue;
    }
    DHSet<Term*> attempted;

    // try subterms of rwTermSS
    NonVariableNonTypeIterator stit(rwTermSS);
    while (stit.hasNext()) {
      auto st = stit.next();
      if (!attempted.insert(st)) {
        stit.right();
        continue;
      }
      auto it = _index->getGeneralizations(st,true);
      while (it.hasNext()) {
        auto qr = it.next();
        if (!qr.clause->noSplits()) {
          continue;
        }
        static RobSubstitution subst;
        TypedTermList trm(st);
        bool resultTermIsVar = qr.term.isVar();
        if(resultTermIsVar){
          TermList querySort = trm.sort();
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          subst.reset();
          if(!subst.match(eqSort, 0, querySort, 1)) {
            continue;
          }
        }
        TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        TermList rhsS=qr.substitution->applyToBoundResult(rhs);
        if(resultTermIsVar){
          rhsS = subst.apply(rhsS, 0);
        }
        VarOrder ext = vo;
        if (!_ord.makeGreater(TermList(st),rhsS,ext)) {
          continue;
        }
        auto vos = ForwardGroundJoinability::order_diff(vo,ext);
        for (auto&& evo : vos) {
          todo.push(std::move(evo));
        }
        goto loop_end;
      }
    }

    for (Term* t : toplevelTerms) {
      auto sideSS = SubstHelper::apply(t, voApp);
      NonVariableNonTypeIterator stit(sideSS, !sideSS->isLiteral());
      while (stit.hasNext()) {
        auto st = stit.next();
        if (!attempted.insert(st)) {
          stit.right();
          continue;
        }
        if (cannotBeGreater(rwTermSS,st)) {
          continue;
        }
        if (rwTermSS == st) {
          continue;
        }
        VarOrder ext = vo;
        if (!rwTermSS->isLiteral() && !_ord.makeGreater(TermList(rwTermSS),TermList(st),ext)) {
          continue;
        }
        auto it = _index->getGeneralizations(st,true);
        while (it.hasNext()) {
          auto qr = it.next();
          if (!qr.clause->noSplits()) {
            continue;
          }
          static RobSubstitution subst;
          TypedTermList trm(st);
          bool resultTermIsVar = qr.term.isVar();
          if(resultTermIsVar){
            TermList querySort = trm.sort();
            TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
            subst.reset();
            if(!subst.match(eqSort, 0, querySort, 1)) {
              continue;
            }
          }
          TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
          TermList rhsS=qr.substitution->applyToBoundResult(rhs);
          if(resultTermIsVar){
            rhsS = subst.apply(rhsS, 0);
          }
          VarOrder ext2 = ext;
          if (!_ord.makeGreater(TermList(st),rhsS,ext2)) {
            continue;
          }
          auto vos = ForwardGroundJoinability::order_diff(vo,ext2);
          for (auto&& evo : vos) {
            todo.push(std::move(evo));
          }
          goto loop_end;
        }
      }
    }

    {
      // finally, try rwTermSS itself
      auto it = _index->getGeneralizations(rwTermSS,true);
      while (it.hasNext()) {
        auto qr = it.next();
        if (!qr.clause->noSplits()) {
          continue;
        }
        static RobSubstitution subst;
        TypedTermList trm(rwTermSS);
        bool resultTermIsVar = qr.term.isVar();
        if(resultTermIsVar){
          TermList querySort = trm.sort();
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          subst.reset();
          if(!subst.match(eqSort, 0, querySort, 1)) {
            continue;
          }
        }
        TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        TermList rhsS=qr.substitution->applyToBoundResult(rhs);
        if(resultTermIsVar){
          rhsS = subst.apply(rhsS, 0);
        }
        VarOrder ext = vo;
        if (!_ord.makeGreater(tgtTermSS,rhsS,ext)) {
          continue;
        }
        if (!_ord.makeGreater(TermList(rwTermSS),rhsS,ext)) {
          continue;
        }
        auto vos = ForwardGroundJoinability::order_diff(vo,ext);
        for (auto&& evo : vos) {
          todo.push(std::move(evo));
        }
        goto loop_end;
      }
    }

    // could not reduce under this partial extension
    return false;
loop_end:
    continue;
  }
  return true;
}

bool ReducibilityChecker::checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp)
{
  ASS(rwTermS->isLiteral() || tgtTermS);
  for (const auto& lit : lits) {
    Stack<Term*> toplevelTerms;
    if (!lit->isEquality()) {
      toplevelTerms.push(lit);
    } else {
      auto comp = _ord.getEqualityArgumentOrder(lit);
      if (comp == Ordering::EQUAL) {
        if (lit->isPositive()) {
          return true;
        } else {
          continue;
        }
      }
      auto t0 = lit->termArg(0);
      auto t1 = lit->termArg(1);
      switch(comp) {
        case Ordering::INCOMPARABLE:
          if (t0.isTerm()) { toplevelTerms.push(t0.term()); }
          if (t1.isTerm()) { toplevelTerms.push(t1.term()); }
          break;
        case Ordering::GREATER:
        case Ordering::GREATER_EQ:
          ASS(t0.isTerm());
          toplevelTerms.push(t0.term());
          break;
        case Ordering::LESS:
        case Ordering::LESS_EQ:
          ASS(t1.isTerm());
          toplevelTerms.push(t1.term());
          break;
        case Ordering::EQUAL:
          ASSERTION_VIOLATION;
      }
    }
    for (Term* t : toplevelTerms) {
      NonVariableNonTypeIterator stit(t, !t->isLiteral());
      while (stit.hasNext()) {
        auto st = stit.next();
        if (!rwTermS->isLiteral() && !Ordering::isGorGEorE(_ord.compare(TermList(rwTermS),TermList(st)))) {
          continue;
        }
        auto it = _index->getGeneralizations(st,true);
        while (it.hasNext()) {
          auto qr = it.next();
          if (!qr.clause->noSplits()) {
            continue;
          }
          static RobSubstitution subst;
          TypedTermList trm(st);
          bool resultTermIsVar = qr.term.isVar();
          if(resultTermIsVar){
            TermList querySort = trm.sort();
            TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
            subst.reset();
            if(!subst.match(eqSort, 0, querySort, 1)) {
              continue;
            }
          }
          TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
          TermList rhsS=qr.substitution->applyToBoundResult(rhs);
          if(resultTermIsVar){
            rhsS = subst.apply(rhsS, 0);
          }
          if (st == rwTermS && _ord.compare(*tgtTermS,rhsS) != Ordering::GREATER) {
            continue;
          }
          if (_ord.compare(TermList(st),rhsS)!=Ordering::GREATER) {
            continue;
          }
          LOG2(exp, "2. rwTermS ", *rwTermS);
          if (st == rwTermS && tgtTermS) {
            LOG2(exp, " with ", *tgtTermS);
          }
          LOG3(exp, *st, " => ", rhsS);
          LOG4(exp, " in ", t, " and ", *lit);
          LOG2(exp, " is reducible by ", *qr.clause);
          return true;
        }
      }
    }
  }
  return false;
}

}