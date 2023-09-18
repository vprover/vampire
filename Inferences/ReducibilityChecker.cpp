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
: /* _reducible(), _nonReducible(), */ _index(index), _ord(ord), _opt(opt) {}

bool ReducibilityChecker::check(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, bool greater)
{
  TIME_TRACE("ReducibilityChecker::check");
  switch (_opt.reducibilityCheck()) {
    case Options::ReducibilityCheck::OFF:
      return false;
    case Options::ReducibilityCheck::LEFTMOST_INNERMOST:
      return checkLeftmostInnermost(cl, rwTermS, subst, result);
    case Options::ReducibilityCheck::SMALLER: {
      vstringstream exp;
      vstringstream exp2;
      vstringstream exp3;
      // auto res = checkSmaller(cl, rwTerm, rwTermS, tgtTermS, subst, result, greater, exp);
      auto res2 = checkSmallerSanityGround(cl, rwTerm, rwTermS, tgtTermS, subst, result, exp2);
      // auto res3 = checkSmallerSanity(cl, rwTerm, rwTermS, tgtTermS, subst, result, exp3);
// #if VDEBUG
      // if (res != res2) {
      //   if (res) {
      //     TIME_TRACE("additional");
      //     env.statistics->skippedSuperpositionGround++;
      //     // cout << "cl " << *cl << " rwTerm " << rwTerm << " rwTermS " << *rwTermS << (tgtTermS ? " tgtTermS " : "") << (tgtTermS ? tgtTermS->toString() : "") << endl;
      //     // cout << "FIRST" << endl << exp.str() << endl;
      //     // cout << "SECOND" << endl << exp2.str() << endl;
      //     // USER_ERROR("x");
      //   } else {
      //     TIME_TRACE("lost");
      //     cout << "cl " << *cl << " rwTerm " << rwTerm << " rwTermS " << *rwTermS << (tgtTermS ? " tgtTermS " : "") << (tgtTermS ? tgtTermS->toString() : "") << endl;
      //     cout << "FIRST" << endl << exp.str() << endl;
      //     cout << "SECOND" << endl << exp2.str() << endl;
      //     USER_ERROR("x");
      //   }
      //   // cout << "cl " << *cl << " rwTerm " << rwTerm << " rwTermS " << *rwTermS << (tgtTermS ? " tgtTermS " : "") << (tgtTermS ? tgtTermS->toString() : "") << endl;
      //   // cout << "FIRST" << endl << exp.str() << endl;
      //   // cout << "SECOND" << endl << exp2.str() << endl;
      //   // USER_ERROR("x");
      // }
// #endif
      return res2;
    }
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::checkLeftmostInnermost(Clause* cl, Term* rwTermS, ResultSubstitution* subst, bool result)
{
  // VarOrders vos;
  // Stack<pair<TermList,TermList>> sides;
  // for (unsigned i = 0; i < cl->numSelected(); i++) {
  //   sides.reset();
  //   getLHSIterator((*cl)[i], subst, result, _ord, sides);

  //   for (auto kv : sides) {
  //     auto side = kv.second;
  //     if (side.isVar()) {
  //       continue;
  //     }
  //     if (subst->isRenamingOn2(kv.first, result)) {
  //       if (!rwTermS->isLiteral() && kv.second.containsSubterm(TermList(rwTermS))) {
  //         return false;
  //       }
  //       continue;
  //     }
  //     PolishSubtermIterator nvi(side.term(), &_nonReducible); // we won't get side itself this way, but we don't need it
  //     while (nvi.hasNext()) {
  //       auto st = nvi.next();
  //       if (st.isVar() || _nonReducible.contains(st.term())) {
  //         continue;
  //       }
  //       if (st.term() == rwTermS) {
  //         // reached rwTerm without finding a reducible term
  //         return false;
  //       }
  //       if (_reducible.find(st.term())) {
  //         return true;
  //       }
  //       // if (cl->rewrites().find(st.term())) {
  //       //   TIME_TRACE("reducible by rule");
  //       //   return true;
  //       // }
  //       if (checkTermReducible(st.term(), nullptr, false, vos)) {
  //         _reducible.insert(st.term());
  //         return true;
  //       }
  //       _nonReducible.insert(st.term());
  //     }
  //     if (side.term() == rwTermS) {
  //       return false;
  //     }
  //   }
  // }
  return false;
}

// inline unsigned termFunctorHash(Term* t, unsigned hash_begin) {
//   unsigned func = t->functor();
//   // std::cout << "will hash funtor " << func << std::endl;
//   return DefaultHash::hash(func, hash_begin);
// }

// unsigned VariantHash::hash(Term* t)
// {
//   static DHMap<unsigned, unsigned char> varCnts;
//   varCnts.reset();

//   unsigned hash = 2166136261u;
//   hash = termFunctorHash(t,hash);

//   SubtermIterator sti(t);
//   while(sti.hasNext()) {
//     TermList tl = sti.next();

//     if (tl.isVar()) {
//       const unsigned varHash = 1u;

//       unsigned char* pcnt;
//       if (varCnts.getValuePtr(tl.var(),pcnt)) {
//         *pcnt = 1;
//       } else {
//         (*pcnt)++;
//       }
//       hash = DefaultHash::hash(varHash, hash);
//     } else {
//       hash = termFunctorHash(tl.term(),hash);
//     }
//   }

//   if (varCnts.size() > 0) {
//     static Stack<unsigned char> varCntHistogram;
//     varCntHistogram.reset();
//     DHMap<unsigned, unsigned char>::Iterator it(varCnts);
//     while (it.hasNext()) {
//       varCntHistogram.push(it.next());
//     }

//     std::sort(varCntHistogram.begin(),varCntHistogram.end());
//     hash = DefaultHash::hash(varCntHistogram, hash);
//   }

//   return hash;
// }

class NonTypeIterator
  : public IteratorCore<std::pair<TermList,TermList>>
{
public:
  NonTypeIterator(const NonTypeIterator&);
  /**
   * If @c includeSelf is false, then only proper subterms of @c term will be included.
   */
  NonTypeIterator(TermList term, TermList termS, DHSet<Term*>& skip, bool includeSelf = false)
  : _stack(8),
    _added(0),
    _skip(skip)
  {
    if (termS.isTerm() && !_skip.insert(termS.term())) {
      return;
    }
    _stack.push(std::make_pair(term,termS));
    if (!includeSelf) {
      NonTypeIterator::next();
    }
  }
  // NonTypeIterator(TermList ts);

  /** true if there exists at least one subterm */
  bool hasNext() { return !_stack.isEmpty(); }
  std::pair<TermList,TermList> next();
  void right();
private:
  /** available non-variable subterms */
  Stack<std::pair<TermList,TermList>> _stack;
  /** the number of non-variable subterms added at the last iteration, used by right() */
  int _added;
  DHSet<Term*>& _skip;
}; // NonTypeIterator

pair<TermList,TermList> NonTypeIterator::next()
{
  auto kv = _stack.pop();
  _added = 0;
  if (kv.first.isTerm()) {
    ASS(kv.second.isTerm());
    ASS_EQ(kv.first.term()->functor(),kv.second.term()->functor());
    for(unsigned i = kv.first.term()->numTypeArguments(); i < kv.first.term()->arity(); i++){
      if (kv.first.term()->nthArgument(i)->isTerm() && !_skip.insert(kv.second.term()->nthArgument(i)->term())) {
        continue;
      }
      _stack.push(std::make_pair(*kv.first.term()->nthArgument(i),*kv.second.term()->nthArgument(i)));
      _added++;
    }
  }
  return kv;
}

void NonTypeIterator::right()
{
  while (_added > 0) {
    _added--;
    _stack.pop();
  }
}

bool ReducibilityChecker::checkSmaller(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, bool greater, vstringstream& exp)
{
  // rwTerm itself will be checked at the end, potentially expensive
  // bool checkRwTerm = !_done.contains(rwTermS); // rwTermS is inserted into _done below
  // NonTypeIterator stit(rwTerm,TermList(rwTermS),_done,false);
  NonVariableNonTypeIterator stit(rwTermS);
  VarOrders vos;
  vos.push(VarOrder()); // start with empty varorder
  if (tgtTermS && !greater) {
    TIME_TRACE("init");
    exp << "try make greater " << *tgtTermS << " " << *rwTermS << endl;
    auto newVos = _ord.makeGreater(*tgtTermS, TermList(rwTermS), vos);
    exp << "newVos " << newVos << endl;
    vos = VarOrder::order_diff(vos,newVos);
    // cout << "diff " << vos << endl;
    VarOrders eq_vos;
    eq_vos.push(VarOrder());
    if (VarOrder::makeEqual(*tgtTermS, TermList(rwTermS), eq_vos[0])) {
      exp << "eq vos " << eq_vos << endl;
      vos = VarOrder::order_diff(vos,eq_vos);
      // cout << "eq diff " << vos << endl;
    }
  }
  // ASS(vos.isNonEmpty());
  exp << "starting with " << vos << endl;
  DHSet<Term*> done;

  Stack<pair<TermList,TermList>> sides(2);
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    sides.reset();
    getLHSIterator((*cl)[i], subst, result, _ord, sides);

    // TODO handle demodulation top-level check
    for (auto kv : sides) {
      auto side = kv.first;
      auto sideS = kv.second;
      if (side.isVar() || sideS.isVar()) {
        continue;
      }
      exp << "side " << sideS << endl;
      NonVariableNonTypeIterator stit(sideS.term(), !sideS.term()->isLiteral());
      while (stit.hasNext()) {
        auto stS = stit.next();
        if (!done.insert(stS)) {
          continue;
        }
        bool variant;
        // cout << "checking " << *stS << endl;
        {
          auto smallerVos = checkTerm(nullptr, stS, rwTermS, subst, result, variant);
          if (smallerVos.isNonEmpty()) {
            // cout << "smaller under " << smallerVos << endl;
            auto redVos = checkTermReducible(stS, nullptr, greater, smallerVos);
            // cout << "smaller and reducible under " << redVos << endl;
            exp << *stS << " reducible under " << redVos << endl;
            vos = VarOrder::order_diff(vos,redVos);
            exp << "remaining " << vos << endl;
            if (vos.isEmpty()) {
              // cout << "COVERED ALL CASES" << endl;
              return true;
            }
          }
        }

        VarOrders eq_vos;
        eq_vos.push(VarOrder());
        if (VarOrder::makeEqual(TermList(stS), TermList(rwTermS), eq_vos[0])) {
          // cout << "eq under " << eq_vos << endl;
          auto redVos = checkTermReducible(stS, tgtTermS, greater, eq_vos);
          // cout << "eq and reducible under " << redVos << endl;
          exp << *stS << " reducible under " << redVos << endl;
          vos = VarOrder::order_diff(vos,redVos);
          exp << "remaining " << vos << endl;
          if (vos.isEmpty()) {
            // cout << "COVERED ALL CASES" << endl;
            return true;
          }
        }
      }
    }
  }
  exp << "remaining at end " << vos << endl;
  return vos.isEmpty();
}

bool ReducibilityChecker::checkSmallerSanity(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, vstringstream& exp)
{
  ASS(rwTermS->isLiteral() || tgtTermS);
  VariableIterator vit(rwTerm);
  while (vit.hasNext()) {
    auto v = vit.next();
    auto t = subst->apply(v, result);
    if (t.isVar()) {
      continue;
    }
    NonVariableNonTypeIterator nvi(t.term(), true);
    while (nvi.hasNext()) {
      auto stS = nvi.next();
      if (!Ordering::isGorGEorE(_ord.compare(TermList(rwTermS),TermList(stS)))) {
        continue;
      }
      auto it = _index->getGeneralizations(stS,true);
      while (it.hasNext()) {
        auto qr = it.next();
        if (!qr.clause->noSplits()) {
          continue;
        }
        static RobSubstitution subst;
        TypedTermList trm(stS);
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
        if (stS == rwTermS && _ord.compare(*tgtTermS,rhsS) != Ordering::GREATER) {
          continue;
        }
        if (_ord.compare(TermList(stS),rhsS)!=Ordering::GREATER) {
          continue;
        }
        exp << "1. rwTermS " << *rwTermS << endl;
        if (stS == rwTermS && tgtTermS) {
          exp << " with " << *tgtTermS << endl;
        }
        exp << *stS << " => " << rhsS << endl;
        exp << " in " << t << " and " << *cl;
        exp << " is reducible by " << *qr.clause << endl;
        return true;
      }
    }
  }
  Stack<pair<TermList,TermList>> sides;
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    sides.reset();
    getLHSIterator((*cl)[i], subst, result, _ord, sides);

    for (auto kv : sides) {
      auto side = kv.first;
      auto sideS = kv.second;
      if (side.isVar() || sideS.isVar()) {
        continue;
      }
      NonVariableNonTypeIterator stit(sideS.term(), !sideS.term()->isLiteral());
      while (stit.hasNext()) {
        auto stS = stit.next();
        if (!rwTermS->isLiteral() && !Ordering::isGorGEorE(_ord.compare(TermList(rwTermS),TermList(stS)))) {
          continue;
        }
        auto it = _index->getGeneralizations(stS,true);
        while (it.hasNext()) {
          auto qr = it.next();
          if (!qr.clause->noSplits()) {
            continue;
          }
          static RobSubstitution subst;
          TypedTermList trm(stS);
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
          if (stS == rwTermS && _ord.compare(*tgtTermS,rhsS) != Ordering::GREATER) {
            continue;
          }
          if (_ord.compare(TermList(stS),rhsS)!=Ordering::GREATER) {
            continue;
          }
          exp << "2. rwTermS " << *rwTermS << endl;
          if (stS == rwTermS && tgtTermS) {
            exp << " with " << *tgtTermS << endl;
          }
          exp << *stS << " => " << rhsS << endl;
          exp << " in " << sideS << " and " << *cl;
          exp << " is reducible by " << *qr.clause << endl;
          return true;
        }
      }
    }
  }
  return false;
}

bool findNextOrder(const DHSet<unsigned>& vars, VarOrder& vo) {
  if (vars.size() < 2) {
    return false;
  }
  while (true) {
    for (unsigned i = 0; i < vo._vars; i++) {
      if (!vars.contains(i)) {
        continue;
      }
      for (unsigned j = i+1; j < vo._vars; j++) {
        if (!vars.contains(j)) {
          continue;
        }
        auto v = static_cast<unsigned>(vo._edges.get(j,i))+1;
        if (v == 4) {
          // overflow
          vo._edges.set(j,i,VarOrder::EQ);
        } else {
          ASS_L(v,4);
          vo._edges.set(j,i,static_cast<VarOrder::Comp>(v));
          goto found;
        }
      }
    }
    return false; // everything overflowed, no more values

found:
    // check transitivity
    for (unsigned i = 0; i < vo._vars; i++) {
      if (!vars.contains(i)) {
        continue;
      }
      for (unsigned j = i+1; j < vo._vars; j++) {
        if (!vars.contains(j)) {
          continue;
        }
        for (unsigned k = j+1; k < vo._vars; k++) {
          if (!vars.contains(k)) {
            continue;
          }
          auto ij = vo.val(i,j);
          auto jk = vo.val(j,k);
          auto ik = vo.val(i,k);
          ASS_NEQ(ij,VarOrder::UNSET);
          ASS_NEQ(jk,VarOrder::UNSET);
          ASS_NEQ(ik,VarOrder::UNSET);
          auto check_triangle = [](VarOrder::Comp ij, VarOrder::Comp jk, VarOrder::Comp ik) {
            if (ij == VarOrder::EQ) {
              return ik == jk;
            } else if (ij == VarOrder::GT && jk != VarOrder::LT) {
              // c >= b > a
              return ik == VarOrder::GT;
            } else if (ij == VarOrder::LT && jk != VarOrder::GT) {
              // c <= b < a
              return ik == VarOrder::LT;
            }
            return true;
          };
          if (!check_triangle(ij,jk,ik) || !check_triangle(ij,ik,jk) || !check_triangle(ik,jk,ij)) {
            goto next;
          }
        }
      }
    }
  return true;
next:
  continue;
  }
  return false;
}

bool ReducibilityChecker::checkSmallerSanityGround(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, vstringstream& exp)
{
  TIME_TRACE("ReducibilityChecker::checkSmallerSanityGround");
  DHSet<unsigned> vars;
  vars.loadFromIterator(iterTraits(vi(new VariableIterator(rwTermS))).map([](TermList v) {
    if (v.var()>=10) {
      cout << "var overflow" << endl;
    }
    return v.var(); }));
  VarOrder vo;
  // start with all EQ
  for (unsigned i = 0; i < vo._vars; i++) {
    if (!vars.contains(i)) {
      continue;
    }
    for (unsigned j = i+1; j < vo._vars; j++) {
      if (!vars.contains(j)) {
        continue;
      }
      vo._edges.set(j,i,VarOrder::EQ);
    }
  }
  do {
    exp << "under " << vo << endl;
    VarOrderEqApplicator voApp(vo);
    auto rwTermSS = SubstHelper::apply(rwTermS, voApp);
    auto tgtTermSS = SubstHelper::apply(*tgtTermS,voApp);
    exp << "with " << *rwTermS << " " << *rwTermSS << endl;
    exp << "rwTerm " << *rwTermS << " " << *rwTermSS << endl;
    exp << "tgtTerm " << tgtTermS->toString() << " " << tgtTermSS << endl;
    if (TermList(rwTermSS)==tgtTermSS || kboGreater(tgtTermSS,TermList(rwTermSS),vo,vars)) {
      exp << "inference redundant" << endl;
      continue;
    }
    bool reduced = false;
    Stack<pair<TermList,TermList>> sides;
    for (unsigned i = 0; i < cl->numSelected(); i++) {
      sides.reset();
      getLHSIterator((*cl)[i], subst, result, _ord, sides);

      for (auto kv : sides) {
        auto side = kv.first;
        auto sideS = kv.second;
        if (side.isVar() || sideS.isVar()) {
          continue;
        }
        auto sideSS = SubstHelper::apply(sideS, voApp);
        exp << "side " << sideS << " " << sideSS << endl;
        NonVariableNonTypeIterator stit(sideSS.term(), !sideS.term()->isLiteral());
        while (stit.hasNext()) {
          auto stS = stit.next();
          exp << "comparing to " << *stS << endl;
          if (!rwTermSS->isLiteral() && rwTermSS != stS && !kboGreater(TermList(rwTermSS),TermList(stS),vo,vars)) {
            continue;
          }
          exp << "greater" << endl;
          auto it = _index->getGeneralizations(stS,true);
          while (it.hasNext()) {
            auto qr = it.next();
            if (!qr.clause->noSplits()) {
              continue;
            }
            static RobSubstitution subst;
            TypedTermList trm(stS);
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
            exp << "comparing tgtTerm to " << *stS << endl;
            if (stS == rwTermSS && !kboGreater(tgtTermSS,rhsS,vo,vars)) {
              continue;
            }
            exp << "comparing term to " << rhsS << endl;
            if (!kboGreater(TermList(stS),rhsS,vo,vars)) {
              continue;
            }
            reduced = true;
            exp << "reducible by " << *stS << " = " << rhsS << endl;
            break;
          }
          if (reduced) {
            break;
          }
        }
        if (reduced) {
          break;
        }
      }
    }
    if (!reduced) {
      exp << "non reducible" << endl;
      return false;
    }
  } while (findNextOrder(vars, vo));
  exp << "reducible under all orders" << endl;
  return true;
}

inline bool cannotBeGreater(Term* t1, Term* t2) {
  return t1->numVarOccs() < t2->numVarOccs() || (~t1->varmap() & t2->varmap()) || t1->weight() < t2->weight();
}

VarOrders ReducibilityChecker::checkTerm(Term* t, Term* tS, Term* rwTermS, ResultSubstitution* subst, bool result, bool& variant)
{
  TIME_TRACE("checkTerm");
  // ASS(!t->isLiteral());
  variant = false;
  if (!rwTermS->isLiteral()) {
    // check if rwTerm can be greater than st
    if (cannotBeGreater(rwTermS, tS)) {
      ASS_NEQ(_ord.compare(TermList(rwTermS),TermList(tS)), Ordering::GREATER);
      return VarOrders(); // empty
    }
    return _ord.makeGreater(TermList(rwTermS),TermList(tS),VarOrder::all());
  }
  return VarOrder::all();
}

// returns VarOrders under which tS is reducible
VarOrders ReducibilityChecker::checkTermReducible(Term* tS, TermList* tgtTermS, bool greater, const VarOrders& initial)
{
  TIME_TRACE(tgtTermS ? "checkTermReducibleRule" : "checkTermReducible");
  // if (_nonReducible.contains(tS)) {
  //   return false;
  // }
  // if (!tgtTermS && _reducible.contains(tS)) {
  //   return true;
  // }
  VarOrders res;
  auto it = _index->getGeneralizations(tS,true);
  // cout << "initial " << initial << endl;
  // bool nonreducible = true;
  while (it.hasNext()) {
    auto qr = it.next();
    // considering reducibility with AVATAR clauses
    // can quickly result in incompleteness
    if (!qr.clause->noSplits()) {
      // nonreducible = false;
      continue;
    }

    static RobSubstitution subst;
    TypedTermList trm(tS);
    bool resultTermIsVar = qr.term.isVar();
    if(resultTermIsVar){
      TermList querySort = trm.sort();
      TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
      subst.reset();
      if(!subst.match(eqSort, 0, querySort, 1)) {
        continue;
      }
    }
    Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
    bool preordered = argOrder==Ordering::LESS || argOrder==Ordering::GREATER;
    if (preordered && !tgtTermS) {
      // _reducible.insert(tS);
      return initial; // reducible unconditionally
    }

    TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
    TermList rhsS=qr.substitution->applyToBoundResult(rhs);
    if(resultTermIsVar){
      rhsS = subst.apply(rhsS, 0);
    }

    // cout << "found " << *tS << " " << rhsS << endl;
    auto vos = initial;
    if (tgtTermS) {
      if (tgtTermS->isTerm() && rhsS.isTerm() && cannotBeGreater(tgtTermS->term(),rhsS.term())) {
        ASS_NEQ(_ord.compare(*tgtTermS,TermList(tS)), Ordering::GREATER);
        continue;
      }
      vos = _ord.makeGreater(*tgtTermS,rhsS,vos);
      // cout << "after tgtTerm " << vos << endl;
    }

    if (!preordered) {
      if (tgtTermS) {
        if (!greater) {
          vos = _ord.makeGreater(TermList(tS),rhsS,vos);
        }
      } else {
        vos = _ord.makeGreater(TermList(tS),rhsS,vos);
      }
    }
    // cout << "after rhsS " << vos << endl;
    for (const auto& vo : vos) {
      if (!contains(res,vo)) {
        res.push(vo);
      }
    }
    // _reducible.insert(tS);
    // return true;
  }
  // if (!tgtTermS && nonreducible) {
  //   _nonReducible.insert(tS);
  // }
  return res;
}

bool ReducibilityChecker::kboGreater(TermList tl1, TermList tl2, const VarOrder& vo, const DHSet<unsigned>& vars)
{
  // cout << "compare " << tl1 << " " << tl2 << endl;
  if (tl1 == tl2) {
    return false;
  }
  if (tl1.isVar()) {
    if (tl2.isVar()) {
      return vo.val(tl1.var(),tl2.var()) == VarOrder::GT;
    }
    return false; //tl2.term()->weight() == tl1.weight() && !tl2.containsSubterm(tl1);
  }
  if (tl2.isVar()) {
    VariableIterator vit(tl1.term());
    while (vit.hasNext()) {
      auto v = vit.next().var();
      if (v == tl2.var() || vo.val(v,tl2.var()) == VarOrder::GT) {
        return true;
      }
    }
    return false;
  }

  auto t1 = tl1.term();
  auto t2 = tl2.term();

  if (t1->weight()<t2->weight()) {
    return false;
  }
  if (t1->weight()==t2->weight()) {
    if (t1->functor()==t2->functor()) {
      // lexicographic case
      bool gt = false;
      for (unsigned i = 0; i < t1->arity(); i++) {
        auto arg1 = *t1->nthArgument(i);
        auto arg2 = *t2->nthArgument(i);
        if (arg1 == arg2) {
          continue;
        }
        if (kboGreater(arg1,arg2,vo,vars)) {
          gt = true;
          break;
        } else {
          return false;
        }
      }
      if (!gt) {
        return false;
      }
    } else {
      if (t1->isSort()) {
        ASS(t2->isSort());
        if (static_cast<const PrecedenceOrdering&>(_ord).compareTypeConPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
          return false;
        }
      } else {
        if (static_cast<const PrecedenceOrdering&>(_ord).compareFunctionPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
          return false;
        }
      }
    }
  }

  // compare variables
  VariableIterator vit(t2);
  DHMap<unsigned,unsigned> varCnts;
  while (vit.hasNext()) {
    auto v = vit.next();
    unsigned* cnt;
    if (!varCnts.getValuePtr(v.var(), cnt, 1)) {
      (*cnt)++;
    }
  }

  VariableIterator vit2(t1);
  unsigned pos = varCnts.size();
  while (vit2.hasNext()) {
    auto v = vit2.next();
    if (!vars.contains(v.var())) {
      continue;
    }
    for (unsigned i = 0; i < vo._vars; i++) {
      if (v.var() == i || vo.val(v.var(),i)==VarOrder::GT) {
        auto ptr = varCnts.findPtr(i);
        if (!ptr || !(*ptr)) {
          continue;
        }
        (*ptr)--;
        if ((*ptr)==0) {
          ASS(pos);
          pos--;
        }
      }
    }
  }
  if (pos) {
    // cout << "compare " << tl1 << " " << tl2 << endl;
    return false;
  }

  return true;
}

}