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

bool ReducibilityChecker::check(Clause* rwClause, Clause* eqClause, Literal* rwLitS, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool eqIsResult)
{
  TIME_TRACE("ReducibilityChecker::check");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  Stack<Literal*> lits;
  // cout << "SUPERPOSITION" << endl;
  // cout << "rwClause ";
  for (unsigned i = 0; i < rwClause->numSelected(); i++) {
    lits.push(subst->apply((*rwClause)[i],!eqIsResult));
    // cout << *lits.top();
    // if (i+1 < rwClause->numSelected()) {
    //   cout << " | ";
    // }
  }
  // cout << endl << "eqClause ";
  for (unsigned i = 0; i < eqClause->numSelected(); i++) {
    lits.push(subst->apply((*eqClause)[i],eqIsResult));
    // cout << *lits.top();
    // if (i+1 < eqClause->numSelected()) {
    //   cout << " | ";
    // }
  }
  // cout << endl;
  // switch (_opt.reducibilityCheck()) {
  //   case Options::ReducibilityCheck::SMALLER: {
  //     vstringstream exp;
  //     return checkSmallerSanity(lits, rwTermS, tgtTermS, exp);
  //   }
  //   case Options::ReducibilityCheck::SMALLER_GROUND: {
  //     vstringstream exp;
  //     return checkSmallerSanityGround(lits, rwLitS, rwTermS, tgtTermS, exp);
  //   }
  //   default:
  //     return false;
  // }
  vstringstream exp, expGr;
  // if (checkSmallerSanity(lits, rwTermS, tgtTermS, exp)) {
  //   ASS_REP(checkSmallerSanityGround(lits, rwLitS, rwTermS, tgtTermS, expGr), exp.str() + expGr.str());
  //   env.statistics->skippedSuperposition++;
  //   return true;
  // }
  if (checkSmallerSanityGround(lits, rwLitS, rwTermS, tgtTermS, expGr)) {
    // cout << expGr.str() << endl;
    env.statistics->skippedSuperpositionGround++;
    return true;
  }
  return false;
  ASSERTION_VIOLATION;
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

bool ReducibilityChecker::checkSmallerSanityGround(const Stack<Literal*>& lits, Literal* rwLitS, Term* rwTermS, TermList* tgtTermS, vstringstream& exp)
{
  TIME_TRACE("ReducibilityChecker::checkSmallerSanityGround");
  // DHSet<unsigned> vars;
  // vars.loadFromIterator(iterTraits(vi(new VariableIterator(rwTermS))).map([](TermList v) { return v.var(); }));
  // VarOrder vo(vars);
  // // if (vars.size()>4) {
  // //   return false;
  // // }
  // unsigned cnt = 0;
  // // Stack<Clause*> cls;
  // while (VarOrder::getVarOrder(vars.size(), cnt++, vo)) {
  //   LOG2(exp, "under ", vo);
  //   VarOrderEqApplicator voApp(vo);
  //   auto rwTermSS = SubstHelper::apply(rwTermS, voApp);
  //   auto tgtTermSS = SubstHelper::apply(*tgtTermS,voApp);
  //   LOG4(exp, "rwTerm ", *rwTermS, " ", *rwTermSS);
  //   LOG4(exp, "tgtTerm ", tgtTermS->toString(), " ", tgtTermSS);
  //   // if r\theta\eta >= l\theta\eta under grounding substitution \eta, the inference is redundant
  //   if (TermList(rwTermSS)==tgtTermSS || kboGreater(tgtTermSS,TermList(rwTermSS),vo,vars)) {
  //     LOG1(exp, "inference redundant");
  //     continue;
  //   }

  //   auto rwLitSS = SubstHelper::apply(rwLitS, voApp);
  //   if (rwLitSS->isEquality()) {
  //     if (EqHelper::isEqTautology(rwLitSS)) {
  //       continue;
  //     }
  //     TermList arg0=*rwLitSS->nthArgument(0);
  //     TermList arg1=*rwLitSS->nthArgument(1);

  //     if (!arg0.containsSubterm(TermList(rwTermSS))) {
  //       if (kboGreater(arg0,arg1,vo,vars)) {
  //         continue;
  //       }
  //     } else if(!arg1.containsSubterm(TermList(rwTermSS))) {
  //       if (kboGreater(arg1,arg0,vo,vars)) {
  //         continue;
  //       }
  //     }
  //   }

  //   bool reduced = false;
  //   bool redundant = false;
  //   for (const auto& lit : lits) {
  //     Stack<Term*> toplevelTerms;
  //     // auto litSS = SubstHelper::apply(lit, voApp);
  //     LOG4(exp, "lit ", *lit, " ", *SubstHelper::apply(lit, voApp));
  //     if (!lit->isEquality()) {
  //       toplevelTerms.push(lit);
  //     } else {
  //       // auto t0 = litSS->termArg(0);
  //       // auto t1 = litSS->termArg(1);
  //       // if (t0 == t1) {
  //       //   if (litSS->isPositive()) {
  //       //     redundant = true;
  //       //     break;
  //       //   } else {
  //       //     continue;
  //       //   }
  //       // }
  //       // auto t0gt = kboGreater(t0,t1,vo,vars);
  //       // auto t1gt = kboGreater(t1,t0,vo,vars);
  //       // ASS(!t0gt || !t1gt);
  //       // if (t0gt) {
  //       //   ASS(t0.isTerm());
  //       //   toplevelTerms.push(t0.term());
  //       // } else if (t1gt) {
  //       //   ASS(t1.isTerm());
  //       //   toplevelTerms.push(t1.term());
  //       // } else {
  //       //   if (t0.isTerm()) { toplevelTerms.push(t0.term()); }
  //       //   if (t1.isTerm()) { toplevelTerms.push(t1.term()); }
  //       // }
  //       auto comp = _ord.getEqualityArgumentOrder(lit);
  //       if (comp == Ordering::EQUAL) {
  //         if (lit->isPositive()) {
  //           redundant = true;
  //           break;
  //         } else {
  //           continue;
  //         }
  //       }
  //       auto t0 = lit->termArg(0);
  //       auto t1 = lit->termArg(1);
  //       switch(comp) {
  //         case Ordering::INCOMPARABLE:
  //           if (t0.isTerm()) { toplevelTerms.push(t0.term()); }
  //           if (t1.isTerm()) { toplevelTerms.push(t1.term()); }
  //           break;
  //         case Ordering::GREATER:
  //         case Ordering::GREATER_EQ:
  //           ASS(t0.isTerm());
  //           toplevelTerms.push(t0.term());
  //           break;
  //         case Ordering::LESS:
  //         case Ordering::LESS_EQ:
  //           ASS(t1.isTerm());
  //           toplevelTerms.push(t1.term());
  //           break;
  //         case Ordering::EQUAL:
  //           ASSERTION_VIOLATION;
  //       }
  //     }

  //     for (Term* t : toplevelTerms) {
  //       TIME_TRACE("side inner");
  //       auto sideSS = SubstHelper::apply(t, voApp);
  //       // auto sideSS = t;
  //       // LOG4(exp, "side ", *t, " ", *sideSS);
  //       NonVariableNonTypeIterator stit(sideSS, !sideSS->isLiteral());
  //       while (stit.hasNext()) {
  //         // TIME_TRACE("term inner");
  //         auto stS = stit.next();
  //         // LOG2(exp, "comparing to ", *stS);
  //         if (!rwTermSS->isLiteral() && rwTermSS != stS && !kboGreater(TermList(rwTermSS),TermList(stS),vo,vars)) {
  //           continue;
  //         }
  //         // LOG1(exp, "greater");
  //         auto it = _index->getGeneralizations(stS,true);
  //         while (it.hasNext()) {
  //           // TIME_TRACE("indexing inner");
  //           auto qr = it.next();
  //           if (!qr.clause->noSplits()) {
  //             continue;
  //           }
  //           static RobSubstitution subst;
  //           TypedTermList trm(stS);
  //           bool resultTermIsVar = qr.term.isVar();
  //           if(resultTermIsVar){
  //             TermList querySort = trm.sort();
  //             TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
  //             subst.reset();
  //             if(!subst.match(eqSort, 0, querySort, 1)) {
  //               continue;
  //             }
  //           }
  //           TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
  //           TermList rhsS=qr.substitution->applyToBoundResult(rhs);
  //           if(resultTermIsVar){
  //             rhsS = subst.apply(rhsS, 0);
  //           }
  //           // LOG2(exp, "comparing tgtTerm to ", *stS);
  //           if (stS == rwTermSS && !kboGreater(tgtTermSS,rhsS,vo,vars)) {
  //             continue;
  //           }
  //           // LOG2(exp, "comparing term to ", rhsS);
  //           if (!kboGreater(TermList(stS),rhsS,vo,vars)) {
  //             continue;
  //           }
  //           reduced = true;
  //           // cls.push(qr.clause);
  //           LOG4(exp, "reducible by ", *stS, " = ", rhsS);
  //           break;
  //         }
  //         if (reduced) {
  //           break;
  //         }
  //       }
  //       if (reduced) {
  //         break;
  //       }
  //     }
  //     if (reduced) {
  //       break;
  //     }
  //   }
  //   if (redundant) {
  //     continue;
  //   }
  //   if (!reduced) {
  //     LOG1(exp, "non reducible");
  //     return false;
  //   }
  // }
  // // cout << "reduced by:" << endl; 
  // // for (const auto& cl : cls) {
  // //   cout << *cl << endl;
  // // }
  // LOG1(exp, "reducible under all orders");
  // return true;
  return false;
}

inline bool cannotBeGreater(Term* t1, Term* t2) {
  return t1->numVarOccs() < t2->numVarOccs() || (~t1->varmap() & t2->varmap()) || t1->weight() < t2->weight();
}

// VarOrders ReducibilityChecker::checkTerm(Term* t, Term* tS, Term* rwTermS, const DHSet<unsigned>& vars)
// {
//   TIME_TRACE("checkTerm");
//   if (!rwTermS->isLiteral()) {
//     // check if rwTerm can be greater than st
//     if (cannotBeGreater(rwTermS, tS)) {
//       ASS_NEQ(_ord.compare(TermList(rwTermS),TermList(tS)), Ordering::GREATER);
//       return VarOrders(); // empty
//     }
//     return _ord.makeGreater(TermList(rwTermS),TermList(tS),VarOrder::all(vars));
//   }
//   return VarOrder::all(vars);
// }

// // returns VarOrders under which tS is reducible
// VarOrders ReducibilityChecker::checkTermReducible(Term* tS, TermList* tgtTermS, bool greater, const VarOrders& initial)
// {
//   TIME_TRACE(tgtTermS ? "checkTermReducibleRule" : "checkTermReducible");
//   // if (_nonReducible.contains(tS)) {
//   //   return false;
//   // }
//   // if (!tgtTermS && _reducible.contains(tS)) {
//   //   return true;
//   // }
//   VarOrders res;
//   auto it = _index->getGeneralizations(tS,true);
//   // cout << "initial " << initial << endl;
//   // bool nonreducible = true;
//   while (it.hasNext()) {
//     auto qr = it.next();
//     // considering reducibility with AVATAR clauses
//     // can quickly result in incompleteness
//     if (!qr.clause->noSplits()) {
//       // nonreducible = false;
//       continue;
//     }

//     static RobSubstitution subst;
//     TypedTermList trm(tS);
//     bool resultTermIsVar = qr.term.isVar();
//     if(resultTermIsVar){
//       TermList querySort = trm.sort();
//       TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
//       subst.reset();
//       if(!subst.match(eqSort, 0, querySort, 1)) {
//         continue;
//       }
//     }
//     Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
//     bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
//     if (preordered && !tgtTermS) {
//       // _reducible.insert(tS);
//       return initial; // reducible unconditionally
//     }

//     TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
//     TermList rhsS=qr.substitution->applyToBoundResult(rhs);
//     if(resultTermIsVar){
//       rhsS = subst.apply(rhsS, 0);
//     }

//     // cout << "found " << *tS << " " << rhsS << endl;
//     auto vos = initial;
//     if (tgtTermS) {
//       if (tgtTermS->isTerm() && rhsS.isTerm() && cannotBeGreater(tgtTermS->term(),rhsS.term())) {
//         ASS_NEQ(_ord.compare(*tgtTermS,TermList(tS)), Ordering::GREATER);
//         continue;
//       }
//       vos = _ord.makeGreater(*tgtTermS,rhsS,vos);
//       // cout << "after tgtTerm " << vos << endl;
//     }

//     if (!preordered) {
//       if (tgtTermS) {
//         if (!greater) {
//           vos = _ord.makeGreater(TermList(tS),rhsS,vos);
//         }
//       } else {
//         vos = _ord.makeGreater(TermList(tS),rhsS,vos);
//       }
//     }
//     // cout << "after rhsS " << vos << endl;
//     for (const auto& vo : vos) {
//       if (!contains(res,vo)) {
//         res.push(vo);
//       }
//     }
//     // _reducible.insert(tS);
//     // return true;
//   }
//   // if (!tgtTermS && nonreducible) {
//   //   _nonReducible.insert(tS);
//   // }
//   return res;
// }

// bool ReducibilityChecker::kboGreater(TermList tl1, TermList tl2, const VarOrder& vo, const DHSet<unsigned>& vars)
// {
//   TIME_TRACE("naive kbo");
//   // cout << "compare " << tl1 << " " << tl2 << endl;
//   if (tl1 == tl2) {
//     return false;
//   }
//   if (tl1.isVar()) {
//     if (tl2.isVar()) {
//       return vo.hasVar(tl1.var()) && vo.hasVar(tl2.var()) && vo.val(tl1.var(),tl2.var()) == VarOrder::GT;
//     }
//     return false; //tl2.term()->weight() == tl1.weight() && !tl2.containsSubterm(tl1);
//   }
//   if (tl2.isVar()) {
//     VariableIterator vit(tl1.term());
//     while (vit.hasNext()) {
//       auto v = vit.next().var();
//       if (v == tl2.var() || (vo.hasVar(v) && vo.hasVar(tl2.var()) && vo.val(v,tl2.var()) == VarOrder::GT)) {
//         return true;
//       }
//     }
//     return false;
//   }

//   auto t1 = tl1.term();
//   auto t2 = tl2.term();

//   if (t1->weight()<t2->weight()) {
//     return false;
//   }
//   if (t1->weight()==t2->weight()) {
//     if (t1->functor()==t2->functor()) {
//       // lexicographic case
//       bool gt = false;
//       for (unsigned i = 0; i < t1->arity(); i++) {
//         auto arg1 = *t1->nthArgument(i);
//         auto arg2 = *t2->nthArgument(i);
//         if (arg1 == arg2) {
//           continue;
//         }
//         if (kboGreater(arg1,arg2,vo,vars)) {
//           gt = true;
//           break;
//         } else {
//           return false;
//         }
//       }
//       if (!gt) {
//         return false;
//       }
//     } else {
//       if (t1->isSort()) {
//         ASS(t2->isSort());
//         if (static_cast<const PrecedenceOrdering&>(_ord).compareTypeConPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
//           return false;
//         }
//       } else {
//         if (static_cast<const PrecedenceOrdering&>(_ord).compareFunctionPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
//           return false;
//         }
//       }
//     }
//   }

//   // compare variables
//   VariableIterator vit(t2);
//   DHMap<unsigned,unsigned> varCnts;
//   while (vit.hasNext()) {
//     auto v = vit.next();
//     unsigned* cnt;
//     if (!varCnts.getValuePtr(v.var(), cnt, 1)) {
//       (*cnt)++;
//     }
//   }

//   VariableIterator vit2(t1);
//   unsigned pos = varCnts.size();
//   while (vit2.hasNext()) {
//     auto v = vit2.next();
//     if (!vars.contains(v.var())) {
//       continue;
//     }
//     DHSet<unsigned>::Iterator vit3(vars);
//     while (vit3.hasNext()) {
//       auto v2 = vit3.next();
//       if (v.var() == v2 || vo.val(v.var(),v2) == VarOrder::GT) {
//         auto ptr = varCnts.findPtr(v2);
//         if (!ptr || !(*ptr)) {
//           continue;
//         }
//         (*ptr)--;
//         if ((*ptr)==0) {
//           ASS(pos);
//           pos--;
//         }
//       }
//     }
//   }
//   if (pos) {
//     // cout << "compare " << tl1 << " " << tl2 << endl;
//     return false;
//   }

//   return true;
// }

}