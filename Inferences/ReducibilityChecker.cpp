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

#include "Lib/BitUtils.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/EqHelper.hpp"

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
: _reducible(), _nonReducible(), _index(index), _ord(ord), _opt(opt) {}

bool ReducibilityChecker::check(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, bool greater)
{
  TIME_TRACE("ReducibilityChecker::check");
  switch (_opt.reducibilityCheck()) {
    case Options::ReducibilityCheck::OFF:
      return false;
    case Options::ReducibilityCheck::LEFTMOST_INNERMOST:
      return checkLeftmostInnermost(cl, rwTermS, subst, result);
    case Options::ReducibilityCheck::SMALLER: {
      auto res = checkSmaller(cl, rwTerm, rwTermS, tgtTermS, subst, result, greater);
#if VDEBUG
      vstringstream str;
      if (res != checkSmallerSanity(cl, rwTerm, rwTermS, tgtTermS, subst, result, str)) {
        cout << "cl " << *cl << " rwTerm " << rwTerm << " rwTermS " << *rwTermS << (tgtTermS ? " tgtTermS " : "") << (tgtTermS ? tgtTermS->toString() : "") << endl;
        cout << str.str() << endl;
        ASSERTION_VIOLATION;
      }
#endif
      return res;
    }
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::checkLeftmostInnermost(Clause* cl, Term* rwTermS, ResultSubstitution* subst, bool result)
{
  Stack<pair<TermList,TermList>> sides;
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    sides.reset();
    getLHSIterator((*cl)[i], subst, result, _ord, sides);

    for (auto kv : sides) {
      auto side = kv.second;
      if (side.isVar()) {
        continue;
      }
      if (subst->isRenamingOn2(kv.first, result)) {
        if (!rwTermS->isLiteral() && kv.second.containsSubterm(TermList(rwTermS))) {
          return false;
        }
        continue;
      }
      PolishSubtermIterator nvi(side.term(), &_nonReducible); // we won't get side itself this way, but we don't need it
      while (nvi.hasNext()) {
        auto st = nvi.next();
        if (st.isVar() || _nonReducible.contains(st.term())) {
          continue;
        }
        if (st.term() == rwTermS) {
          // reached rwTerm without finding a reducible term
          return false;
        }
        if (_reducible.find(st.term())) {
          return true;
        }
        // if (cl->rewrites().find(st.term())) {
        //   TIME_TRACE("reducible by rule");
        //   return true;
        // }
        if (checkTermReducible(st.term(), nullptr, false)) {
          _reducible.insert(st.term());
          return true;
        }
        _nonReducible.insert(st.term());
      }
      if (side.term() == rwTermS) {
        return false;
      }
    }
  }
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

bool ReducibilityChecker::checkSmaller(Clause* cl, TermList rwTerm, Term* rwTermS, TermList* tgtTermS, ResultSubstitution* subst, bool result, bool greater)
{
  // rwTerm itself will be checked at the end, potentially expensive
  bool checkRwTerm = !_done.contains(rwTermS); // rwTermS is inserted into _done below
  NonTypeIterator stit(rwTerm,TermList(rwTermS),_done,false);
  bool toplevelCheck = cl->length()==1 && (*cl)[0]->isEquality() && (*cl)[0]->isPositive();
  while (stit.hasNext()) {
    auto kv = stit.next();
    auto st = kv.first;
    auto stS = kv.second;
    if (st.isVar()) {
      // these need to be checked only once, here
      if (stS.isTerm()) {
        NonVariableNonTypeIterator inner(stS.term(),true);
        while(inner.hasNext()) {
          auto ins = inner.next();
          if (!_done.insert(ins)) {
            inner.right();
            continue;
          }
          if (checkTermReducible(ins, nullptr, greater)) {
            return true;
          }
        }
      }
      continue;
    }
    auto t = st.term();
    auto tS = stS.term();
    if ((!toplevelCheck || (st != (*cl)[0]->termArg(0) && st != (*cl)[0]->termArg(1))) &&
        t->weight() == tS->weight() && BitUtils::oneBits(t->varmap()) == BitUtils::oneBits(tS->varmap()) && t->numVarOccs() == tS->numVarOccs()) {
      ASS(subst->isRenamingOn2(TermList(t),result));
      NonVariableNonTypeIterator inner(tS,true);
      while(inner.hasNext()) {
        TIME_TRACE("extra variant added");
        auto innerT = inner.next();
        _nonReducible.insert(innerT);
      }
      stit.right();
      continue;
    }
    if (checkTermReducible(tS, nullptr, greater)) {
      return true;
    }
  }

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
      NonTypeIterator stit(side, sideS, _done, !sideS.term()->isLiteral());
      while (stit.hasNext()) {
        auto kv = stit.next();
        auto st = kv.first;
        auto stS = kv.second;
        if (st.isVar()) {
          continue;
        }
        auto t = st.term();
        auto tS = stS.term();
        bool variant;
        if (!checkTerm(t, tS, rwTermS, subst, result, variant)) {
          if ((!toplevelCheck || st != side) && variant) {
            NonVariableNonTypeIterator inner(tS,true);
            while(inner.hasNext()) {
              TIME_TRACE("extra variant added");
              auto innerT = inner.next();
              _nonReducible.insert(innerT);
            }
            stit.right();
          }
          continue;
        }
        if (checkTermReducible(tS, nullptr, greater)) {
          return true;
        }
      }
    }
  }
  if (subst->isRenamingOn2(rwTerm, result)) {
    return false;
  }
  if (checkRwTerm && !rwTermS->isLiteral() && checkTermReducible(rwTermS, tgtTermS, greater)) {
    return true;
  }
  return false;
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
        exp << "rwTermS " << *rwTermS << endl;
        exp << *stS;
        if (stS == rwTermS && tgtTermS) {
          exp << " with " << *tgtTermS;
        }
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
          exp << "rwTermS " << *rwTermS << endl;
          exp << *stS;
          if (stS == rwTermS && tgtTermS) {
            exp << " with " << *tgtTermS;
          }
          exp << " in " << sideS << " and " << *cl;
          exp << " is reducible by " << *qr.clause << endl;
          return true;
        }
      }
    }
  }
  return false;
}

inline bool cannotBeGreater(Term* t1, Term* t2) {
  return t1->numVarOccs() < t2->numVarOccs() || (~t1->varmap() & t2->varmap()) || t1->weight() < t2->weight();
}

bool ReducibilityChecker::checkTerm(Term* t, Term* tS, Term* rwTermS, ResultSubstitution* subst, bool result, bool& variant)
{
  TIME_TRACE("checkTerm");
  ASS(!t->isLiteral());
  variant = false;
  // check if variant (including subterms)
  if (t->weight() == tS->weight() && BitUtils::oneBits(t->varmap()) == BitUtils::oneBits(tS->varmap()) && t->numVarOccs() == tS->numVarOccs()) {
    ASS(subst->isRenamingOn2(TermList(t),result));
    variant = true;
    return false;
  }
  if (!rwTermS->isLiteral()) {
    // check if rwTerm can be greater than st
    if (cannotBeGreater(rwTermS, tS)) {
      ASS_NEQ(_ord.compare(TermList(rwTermS),TermList(tS)), Ordering::GREATER);
      return false;
    }
    if (_ord.compare(TermList(rwTermS),TermList(tS)) != Ordering::GREATER) {
      return false;
    }
  }
  return true;
}

bool ReducibilityChecker::checkTermReducible(Term* tS, TermList* tgtTermS, bool greater)
{
  TIME_TRACE(tgtTermS ? "checkTermReducibleRule" : "checkTermReducible");
  if (_nonReducible.contains(tS)) {
    return false;
  }
  if (!tgtTermS && _reducible.contains(tS)) {
    return true;
  }
  auto it = _index->getGeneralizations(tS,true);
  bool nonreducible = true;
  while (it.hasNext()) {
    auto qr = it.next();
    // considering reducibility with AVATAR clauses
    // can quickly result in incompleteness
    if (!qr.clause->noSplits()) {
      nonreducible = false;
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
      _reducible.insert(tS);
      return true;
    }

    TermList rhs=EqHelper::getOtherEqualitySide(qr.literal,qr.term);
    TermList rhsS=qr.substitution->applyToBoundResult(rhs);
    if(resultTermIsVar){
      rhsS = subst.apply(rhsS, 0);
    }

    if (tgtTermS) {
      if (tgtTermS->isTerm() && rhsS.isTerm() && cannotBeGreater(tgtTermS->term(),rhsS.term())) {
        ASS_NEQ(_ord.compare(*tgtTermS,TermList(tS)), Ordering::GREATER);
        continue;
      }
      if (_ord.compare(*tgtTermS,rhsS) != Ordering::GREATER) {
        continue;
      }
    }

    if (!preordered) {
      if (tgtTermS) {
        if (!greater && _ord.compare(TermList(tS),rhsS)!=Ordering::GREATER) {
          continue;
        }
      } else {
        if (_ord.compare(TermList(tS),rhsS)!=Ordering::GREATER) {
          continue;
        }
      }
    }
    _reducible.insert(tS);
    return true;
  }
  if (!tgtTermS && nonreducible) {
    _nonReducible.insert(tS);
  }
  return false;
}

}