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

void ReducibilityChecker::preprocessClause(Clause* cl)
{
  TIME_TRACE("ReducibilityChecker::preprocessClause");
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    Literal* lit=(*cl)[i];
    auto lhsi = EqHelper::getSuperpositionLHSIterator(lit, _ord, _opt);
    while (lhsi.hasNext()) {
      auto side = lhsi.next();
      if (side.isVar()) {
        continue;
      }

      Stack<VarOrder> todo;
      Stack<VarOrder> rest;
      todo.push(VarOrder());
      while (todo.isNonEmpty()) {
        auto vo = todo.pop();
        VarOrder::EqApplicator voApp(vo);
        auto sideS = SubstHelper::apply(side, voApp);
        NonVariableNonTypeIterator stit(sideS.term());
        while (stit.hasNext()) {
          auto st = stit.next();
          auto it = _index->getGeneralizations(st,true);
          while (it.hasNext()) {
            auto qr = it.next();
            TermList rhsS;
            if (!getDemodulationRHSCodeTree(qr, st, rhsS)) {
              continue;
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
        if (sideS.isVar()) {
          continue;
        }
        {
          auto tgtTermS = SubstHelper::apply(EqHelper::getOtherEqualitySide(lit,side), voApp);
          auto it = _index->getGeneralizations(sideS.term(),true);
          while (it.hasNext()) {
            auto qr = it.next();
            TermList rhsS;
            if (!getDemodulationRHSCodeTree(qr, sideS.term(), rhsS)) {
              continue;
            }
            VarOrder ext = vo;
            if (!_ord.makeGreater(tgtTermS,rhsS,ext)) {
              continue;
            }
            if (!_ord.makeGreater(TermList(sideS),rhsS,ext)) {
              continue;
            }
            auto vos = ForwardGroundJoinability::order_diff(vo,ext);
            for (auto&& evo : vos) {
              todo.push(std::move(evo));
            }
            goto loop_end;
          }
        }
        rest.push(vo);
        // cout << "cached " << vo.to_string() << " for " << side << " in " << *lit << " in " << *cl << endl;
loop_end:
        continue;
      }
      // if (rest.isEmpty()) {
      //   cout << "cached " << side << " in " << *lit << " in " << *cl << endl;
      // }
      _uselessLHSCache.insert(make_pair(side,EqHelper::getOtherEqualitySide(lit,side)), rest.isEmpty());
    }
  }
}

ReducibilityChecker::ReducibilityChecker(DemodulationLHSIndex* index, const Ordering& ord, const Options& opt)
: _index(index), _ord(ord), _opt(opt) {}

bool ReducibilityChecker::checkSup(Clause* rwClause, Clause* eqClause, Literal* eqLit, TermList eqLHS, ResultSubstitution* subst, bool eqIsResult)
{
  TIME_TRACE("ReducibilityChecker::checkSup");
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
      return checkSmaller2(lits, rwTermS, &tgtTermS, exp);
      // return checkSmaller(lits, rwTermS, &tgtTermS, eqClause, eqLit, eqLHS, subst, eqIsResult, exp);
    }
    default:
      return false;
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::checkBR(Clause* queryClause, Clause* resultClause, ResultSubstitution* subst)
{
  TIME_TRACE("ReducibilityChecker::checkBR");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  Stack<Literal*> lits;
  for (unsigned i = 0; i < queryClause->numSelected(); i++) {
    lits.push(subst->applyToQuery((*queryClause)[i]));
  }
  for (unsigned i = 0; i < resultClause->numSelected(); i++) {
    lits.push(subst->applyToResult((*resultClause)[i]));
  }
  switch (_opt.reducibilityCheck()) {
    case Options::ReducibilityCheck::SMALLER: {
      vstringstream exp;
      return checkSmallerSanity(lits, nullptr, nullptr, exp);
    }
    case Options::ReducibilityCheck::SMALLER_GROUND: {
      vstringstream exp;
      return checkSmaller2(lits, nullptr, nullptr, exp);
      // return checkSmaller(lits, rwTermS, &tgtTermS, eqClause, eqLit, eqLHS, subst, eqIsResult, exp);
    }
    default:
      return false;
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::checkLiteral(Literal* lit)
{
  TIME_TRACE("ReducibilityChecker::checkLiteral");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  Stack<Literal*> lits;
  lits.push(lit);
  switch (_opt.reducibilityCheck()) {
    case Options::ReducibilityCheck::SMALLER: {
      vstringstream exp;
      return checkSmallerSanity(lits, nullptr, nullptr, exp);
    }
    case Options::ReducibilityCheck::SMALLER_GROUND: {
      vstringstream exp;
      return checkSmaller2(lits, nullptr, nullptr, exp);
      // return checkSmaller(lits, rwTermS, &tgtTermS, eqClause, eqLit, eqLHS, subst, eqIsResult, exp);
    }
    default:
      return false;
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS)
{
  if (!qr.clause->noSplits()) {
    return false;
  }
  static RobSubstitution subst;
  TypedTermList trm(lhsS);
  bool resultTermIsVar = qr.term.isVar();
  if (resultTermIsVar) {
    TermList querySort = trm.sort();
    TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
    subst.reset();
    if (!subst.match(eqSort, 0, querySort, 1)) {
      return false;
    }
  }
  TermList rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
  rhsS = qr.substitution->applyToBoundResult(rhs);
  if (resultTermIsVar) {
    rhsS = subst.apply(rhsS, 0);
  }
  return true;
}

void ReducibilityChecker::clauseActivated(Clause* cl)
{
  TIME_TRACE("ReducibilityChecker::clauseActivated");
  if (cl->length()!=1 || !cl->noSplits()) {
    return;
  }

  Stack<Term*> toUpdate;

  Literal* lit=(*cl)[0];
  auto lhsi = EqHelper::getDemodulationLHSIterator(lit, true, _ord, _opt);
  while (lhsi.hasNext()) {
    auto lhs = lhsi.next();
    auto qrit = _tis.getInstances(lhs, true);
    while (qrit.hasNext()) {
      auto qr = qrit.next();
      TermList rhs=EqHelper::getOtherEqualitySide(lit, lhs);
      TermList lhsS=qr.term;
      TermList rhsS;

      if(!qr.substitution->isIdentityOnResultWhenQueryBound()) {
        //When we apply substitution to the rhs, we get a term, that is
        //a variant of the term we'd like to get, as new variables are
        //produced in the substitution application.
        //We'd rather rename variables in the rhs, than in the whole clause
        //that we're simplifying.
        TermList lhsSBadVars=qr.substitution->applyToQuery(lhs);
        TermList rhsSBadVars=qr.substitution->applyToQuery(rhs);
        Renaming rNorm, qNorm, qDenorm;
        rNorm.normalizeVariables(lhsSBadVars);
        qNorm.normalizeVariables(lhsS);
        qDenorm.makeInverse(qNorm);
        ASS_EQ(lhsS,qDenorm.apply(rNorm.apply(lhsSBadVars)));
        rhsS=qDenorm.apply(rNorm.apply(rhsSBadVars));
      } else {
        rhsS=qr.substitution->applyToBoundQuery(rhs);
      }

      auto t = static_cast<Term*>(qr.literal);
      auto e = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
      ASS(e);
      if (qr.term.term() == t && _ord.isGreater(TermList(t),rhsS)) {
        e->reducesTo.push(rhsS);
      }
      toUpdate.push(t);
    }
  }
  while (toUpdate.isNonEmpty()) {
    auto t = toUpdate.pop();
    auto e = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
    ASS(e);
    e->valid = false;
    for (const auto& st : e->superTerms) {
      toUpdate.push(st);
    }
  }
}

ReducibilityChecker::ReducibilityEntry* ReducibilityChecker::isTermReducible(Term* t)
{
  ReducibilityEntry* vos = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
  TIME_TRACE(vos ? "ReducibilityChecker::isTermReducible" : "ReducibilityChecker::isTermReducibleFirst");
  if (vos && vos->valid) {
    return vos;
  }
  if (!vos) {
    vos = new ReducibilityEntry();
    t->setReducibilityInfo(vos);
    // TODO eventually clear up the index
    _tis.insert(TypedTermList(t), static_cast<Literal*>(t), nullptr);
    for (unsigned i = t->numTypeArguments(); i < t->arity(); i++) {
      auto arg = t->nthArgument(i);
      if (arg->isVar()) {
        continue;
      }
      auto arg_vos = isTermReducible(arg->term());
      arg_vos->superTerms.push(t);
    }
    auto it = _index->getGeneralizations(t,true);
    while (it.hasNext()) {
      auto qr = it.next();
      TermList rhsS;
      if (!getDemodulationRHSCodeTree(qr, t, rhsS)) {
        continue;
      }
      if (!_ord.isGreater(TermList(t),rhsS)) {
        continue;
      }
      // reduced, add it to the reduced stack
      vos->reducesTo.push(rhsS);
    }
  }
  Stack<VarOrder> todo;
  for (const auto& vo : vos->rest) {
    todo.push(vo);
  }
  vos->rest.reset();
  while (todo.isNonEmpty()) {
    auto vo = todo.pop();
    for (unsigned i = t->numTypeArguments(); i < t->arity(); i++) {
      auto arg = t->nthArgument(i);
      if (arg->isVar()) {
        continue;
      }
      auto arg_vos = isTermReducible(arg->term());
      for (const auto& red : arg_vos->reduced) {
        VarOrder ext = vo;
        if (ext.tryExtendWith(red)) {
          auto diff = ForwardGroundJoinability::order_diff(vo,ext);
          for (auto&& evo : diff) {
            todo.push(std::move(evo));
          }
          vos->reduced.push(ext);
          goto loop_end;
        }
      }
    }
    {
      VarOrder::EqApplicator voApp(vo);
      auto tS = SubstHelper::apply(t, voApp);
      auto it = _index->getGeneralizations(tS,true);
      while (it.hasNext()) {
        auto qr = it.next();
        TermList rhsS;
        if (!getDemodulationRHSCodeTree(qr, tS, rhsS)) {
          continue;
        }
        VarOrder ext = vo;
        if (!_ord.makeGreater(TermList(tS),rhsS,ext)) {
          continue;
        }
        auto diff = ForwardGroundJoinability::order_diff(vo,ext);
        for (auto&& evo : diff) {
          todo.push(std::move(evo));
        }
        // reduced, add it to the reduced stack
        vos->reduced.push(ext);
        goto loop_end;
      }
      // could not reduce under this vo, add it to the rest and save it into the index
      vos->rest.push(vo);
      _tis.insert(TypedTermList(tS), static_cast<Literal*>(t), nullptr);
    }
loop_end:
    continue;
  }
  if (vos->rest.isEmpty()) {
    vos->reduced.reset();
    vos->reduced.push(VarOrder());
  }
  if (vos->rest.size()==1 && vos->rest[0].size()==2 && vos->reduced.size()>2) {
    VarOrder vo;
    auto newReduced = ForwardGroundJoinability::order_diff(vo, vos->rest[0]);
    vos->reduced.reset();
    for (const auto& vo : newReduced) {
      vos->reduced.push(vo);
    }
  }
  vos->valid = true;
  return vos;
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

    // VarOrder ext = vo;
    // if (_ord.makeGreater(tgtTermSS,TermList(rwTermSS),ext)) {
    //   auto vos = ForwardGroundJoinability::order_diff(vo,ext);
    //   for (auto&& evo : vos) {
    //     todo.push(std::move(evo));
    //   }
    //   continue;
    // }
    DHSet<Term*> attempted;

    // try subterms of rwTermSS
    NonVariableNonTypeIterator stit(rwTermSS);
    while (stit.hasNext()) {
      auto st = stit.next();
      if (!attempted.insert(st)) {
        stit.right();
        continue;
      }

      auto ptr = isTermReducible(st);
      for (const auto& other : ptr->reduced) {
        VarOrder ext = vo;
        if (ext.tryExtendWith(other)) {
          auto vos = ForwardGroundJoinability::order_diff(vo,ext);
          for (auto&& evo : vos) {
            todo.push(std::move(evo));
          }
          goto loop_end;
        }
      }

      // auto it = _index->getGeneralizations(st,true);
      // while (it.hasNext()) {
      //   auto qr = it.next();
      //   TermList rhsS;
      //   if (!getDemodulationRHSCodeTree(qr, st, rhsS)) {
      //     continue;
      //   }
      //   VarOrder ext = vo;
      //   if (!_ord.makeGreater(TermList(st),rhsS,ext)) {
      //     continue;
      //   }
      //   // cout << "not cached for " << *st << " -> " << rhsS << endl;
      //   // cout << "current " << vo.to_string() << endl;
      //   // cout << "ext " << ext.to_string() << endl;
      //   // cout << "reduced " << endl;
      //   // for (const auto& vo : ptr->reduced) {
      //   //   cout << vo.to_string() << endl;
      //   // }
      //   // cout << "rest " << endl;
      //   // for (const auto& vo : ptr->rest) {
      //   //   cout << vo.to_string() << endl;
      //   // }
      //   // USER_ERROR("x");
      //   auto vos = ForwardGroundJoinability::order_diff(vo,ext);
      //   for (auto&& evo : vos) {
      //     todo.push(std::move(evo));
      //   }
      //   goto loop_end;
      // }
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

        auto ptr = isTermReducible(st);
        for (const auto& other : ptr->reduced) {
          VarOrder ext2 = ext;
          if (ext2.tryExtendWith(other)) {
            auto vos = ForwardGroundJoinability::order_diff(vo,ext2);
            for (auto&& evo : vos) {
              todo.push(std::move(evo));
            }
            goto loop_end;
          }
        }

        // auto it = _index->getGeneralizations(st,true);
        // while (it.hasNext()) {
        //   auto qr = it.next();
        //   TermList rhsS;
        //   if (!getDemodulationRHSCodeTree(qr, st, rhsS)) {
        //     continue;
        //   }
        //   VarOrder ext2 = ext;
        //   if (!_ord.makeGreater(TermList(st),rhsS,ext2)) {
        //     continue;
        //   }
        //   auto vos = ForwardGroundJoinability::order_diff(vo,ext2);
        //   for (auto&& evo : vos) {
        //     todo.push(std::move(evo));
        //   }
        //   goto loop_end;
        // }
      }
    }

    {
      // finally, try rwTermSS itself
      auto it = _index->getGeneralizations(rwTermSS,true);
      while (it.hasNext()) {
        auto qr = it.next();
        TermList rhsS;
        if (!getDemodulationRHSCodeTree(qr, rwTermSS, rhsS)) {
          continue;
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

// cheaper but returns more false negatives
bool ReducibilityChecker::checkSmaller2(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp)
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
          if (lit->isPositive()) {
            return true;
          }
          break;
          // ASSERTION_VIOLATION;
      }
    }
  }
  // DHSet<Term*> attempted;

  for (Term* side : toplevelTerms) {
    NonVariableNonTypeIterator stit(side, !side->isLiteral());
    while (stit.hasNext()) {
      auto st = stit.next();
      // if (!attempted.insert(st)) {
      //   stit.right();
      //   continue;
      // }
      if (rwTermS && cannotBeGreater(rwTermS, st)) {
        continue;
      }
      if (rwTermS && !_ord.isGreater(TermList(rwTermS),TermList(st))) {
        continue;
      }

      auto ptr = isTermReducible(st);
      ASS(ptr->valid);
      if (ptr->rest.isEmpty()) {
        return true;
      }
      stit.right();
    }
  }

  if (rwTermS) {
    auto ptr = isTermReducible(rwTermS);
    ASS(ptr->valid);
    for (const auto& rhs : ptr->reducesTo) {
      if (!_ord.isGreater(*tgtTermS,rhs)) {
        continue;
      }
      return true;
    }
  }
  return false;
}

bool ReducibilityChecker::checkSmallerSanity(const Stack<Literal*>& lits, Term* rwTermS, TermList* tgtTermS, vstringstream& exp)
{
  for (const auto& lit : lits) {
    Stack<Term*> toplevelTerms;
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
          if (lit->isPositive()) {
            return true;
          }
          break;
          // ASSERTION_VIOLATION;
      }
    }
    for (Term* t : toplevelTerms) {
      NonVariableNonTypeIterator stit(t, !t->isLiteral());
      while (stit.hasNext()) {
        auto st = stit.next();
        if (!rwTermS || !Ordering::isGorGEorE(_ord.compare(TermList(rwTermS),TermList(st)))) {
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
          if (rwTermS) {
            LOG2(exp, "2. rwTermS ", *rwTermS);
          }
          if (st == rwTermS && tgtTermS) {
            LOG2(exp, " tgtTermS ", *tgtTermS);
          }
          LOG3(exp, *st, " => ", rhsS);
          LOG4(exp, " in ", *t, " and ", *lit);
          LOG2(exp, " is reducible by ", *qr.clause);
          return true;
        }
      }
    }
  }
  return false;
}

}