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
#include "Lib/SharedSet.hpp"

#include "Shell/Statistics.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/FlatTerm.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/VarOrder.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/RewritingData.hpp"

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

class CustomIterator
  : public IteratorCore<std::tuple<TermList,TermList,FlatTerm::Entry*>>
{
public:
  CustomIterator(TermList term, TermList termS, FlatTerm* ft, DHSet<Term*>& done, bool includeSelf=false)
  : _stack(8),
    _added(0),
    _done(done)
  {
    if (term.isTerm() && !term.term()->isSort() && _done.insert(termS.term())) {
      ASS(ft->data()->isFun());
      _stack.push(std::make_tuple(term,termS,ft->data()));
      if (!includeSelf) {
        CustomIterator::next();
      }
    }
  }

  /** true if there exists at least one subterm */
  bool hasNext() { return !_stack.isEmpty(); }
  std::tuple<TermList,TermList,FlatTerm::Entry*> next();
  void right();
private:
  /** available subterms */
  Stack<std::tuple<TermList,TermList,FlatTerm::Entry*>> _stack;
  /** the number of subterms added at the last iteration, used by right() */
  int _added;
  DHSet<Term*>& _done;
}; // CustomIterator

size_t getFTEntryCount2(Term* t)
{
  //functionEntryCount entries per function and one per variable
  return t->weight()*FlatTerm::functionEntryCount-(FlatTerm::functionEntryCount-1)*t->numVarOccs();
}

std::tuple<TermList,TermList,FlatTerm::Entry*> CustomIterator::next()
{
  // TIME_TRACE("CustomIterator::next");
  auto tp = _stack.pop();
  _added = 0;
  ASS(get<0>(tp).isTerm());
  ASS(get<1>(tp).isTerm());
  auto t = get<0>(tp).term();
  auto tS = get<1>(tp).term();
  auto ft_e = get<2>(tp);

  Signature::Symbol* sym;
  if (t->isLiteral()) {
    sym = env.signature->getPredicate(t->functor());
  } else{
    sym = env.signature->getFunction(t->functor());
  }
  // unsigned taArity; 
  unsigned arity;

  if(t->isLiteral() && static_cast<Literal*>(t)->isEquality()){
    // taArity = 0;
    arity = 2;
  } else {
    // taArity = sym->numTypeArguments();
    arity = sym->arity();
  }

  TermList* ts;
  TermList* tsS;
  size_t cnt = FlatTerm::functionEntryCount;
  ft_e->expand();
  for(unsigned i = 0; i < arity; i++){
    ts = t->nthArgument(i);
    tsS = tS->nthArgument(i);
    auto e = ft_e + cnt;

    if (ts->isTerm() && !ts->term()->isSort() && _done.insert(tsS->term())) {
      _stack.push(std::make_tuple(*ts, *tsS, e));
      _added++;
    }
    if (tsS->isTerm()) {
      cnt += e[2].number();
    } else {
      cnt++;
    }
  }
  return tp;
}

/**
 * Skip all subterms of the terms returned by the last call to next()
 */
void CustomIterator::right()
{
  while (_added > 0) {
    _added--;
    _stack.pop();
  }
} // CustomIterator::right




bool argReduced(Term* t) {
  return t->isReduced() && static_cast<ReducibilityChecker::ReducibilityEntry*>(t->reducibilityInfo())->reducesTo.isEmpty();
}

ReducibilityChecker::ReducibilityChecker(DemodulationLHSIndex* index, UnitClauseLiteralIndex* litIndex, const Ordering& ord, const Options& opt)
: _index(index), _litIndex(litIndex), _ord(ord), _opt(opt), _rwTermState(_ord.createState()) {}

bool ReducibilityChecker::pushSidesFromLiteral(Literal* lit, ResultSubstitution* subst, bool result, Term* rwTermS, bool& litIncomparable)
{
  _sidesToCheck.reset();
  litIncomparable = false;

  if (!lit->isEquality()) {
    _sidesToCheck.push(make_pair(TermList(lit),subst->apply(lit,result)));
    return false;
  }

  auto t0 = lit->termArg(0);
  auto t1 = lit->termArg(1);
  auto comp = _ord.getEqualityArgumentOrder(lit);
  switch (comp) {
    case Ordering::INCOMPARABLE: {
      auto t0s = subst->apply(t0,result);
      auto t1s = subst->apply(t1,result);
      switch (_ord.compare(t0s,t1s)) {
        case Ordering::INCOMPARABLE:
          if (t0s.isTerm() && t0s.containsSubterm(TermList(rwTermS))) {
            _sidesToCheck.push(make_pair(t0,t0s.term()));
          }
          if (t1s.isTerm() && t1s.containsSubterm(TermList(rwTermS))) {
            _sidesToCheck.push(make_pair(t1,t1s.term()));
          }
          litIncomparable = true;
          break;
        case Ordering::GREATER:
        case Ordering::GREATER_EQ:
          if (t0s.isTerm()) {
            ASS(t0s.containsSubterm(TermList(rwTermS)));
            _sidesToCheck.push(make_pair(t0,t0s.term()));
          }
          break;
        case Ordering::LESS:
        case Ordering::LESS_EQ:
          if (t1s.isTerm()) {
            ASS(t1s.containsSubterm(TermList(rwTermS)));
            _sidesToCheck.push(make_pair(t1,t1s.term()));
          }
          break;
        case Ordering::EQUAL:
          if (lit->isPositive()) { return true; } // we got a tautology
          break;
      }
      break;
    }
    case Ordering::GREATER:
    case Ordering::GREATER_EQ: {
      ASS(t0.isTerm());
      auto t0s = subst->apply(t0,result);
      ASS(t0s.containsSubterm(TermList(rwTermS)));
      _sidesToCheck.push(make_pair(t0,t0s.term()));
      break;
    }
    case Ordering::LESS:
    case Ordering::LESS_EQ: {
      ASS(t1.isTerm());
      auto t1s = subst->apply(t1,result);
      ASS(t1s.containsSubterm(TermList(rwTermS)));
      _sidesToCheck.push(make_pair(t1,t1s.term()));
      break;
    }
    case Ordering::EQUAL: {
      if (lit->isPositive()) { return true; }
      break;
    }
  }
  return false;
}

struct OneEqBinder {
  bool bind(unsigned var, TermList term)
  {
    if (term.isTerm()) {
      return false;
    }
    if (term.var()==var) {
      return true;
    }
    if (bound) {
      if (b == var && v == term.var()) {
        return true;
      }
      if (b == term.var() && v == var) {
        return true;
      }
      return false;
    }
    bound = true;
    b = var;
    v = term.var();
    return true;
  }
  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
  unsigned b;
  unsigned v;
  bool bound = false;
};

struct EqBinder {
  bool bind(unsigned var, TermList term)
  {
    if (term.isTerm()) {
      return false;
    }
    return vo.add_eq(var,term.var());
  }
  void specVar(unsigned var, TermList term)
  { ASSERTION_VIOLATION; }
  VarOrder vo;
};

struct Binder {
  bool bind(unsigned var, TermList term)
  {
    if (term.isTerm()) {
      renaming = false;
      return true;
    }
    TermList* inserted;
    if (_map.getValuePtr(var, inserted, term)) {
      if (!_vrange.insert(term.var())) {
        renaming = false;
      }
      return true;
    }
    return *inserted == term;
  }

  void specVar(unsigned var, TermList term) const
  {
    ASSERTION_VIOLATION;
  }

  void reset() {
    _map.reset();
    _vrange.reset();
  }

  bool renaming = true;
  DHMap<unsigned,TermList> _map;
  DHSet<unsigned> _vrange;
};

struct Binder2 {
  bool bind(unsigned var, TermList term)
  {
    if (term.isTerm()) {
      bindsTerm = true;
      return true;
    }
    TermList* inserted;
    if (_map.getValuePtr(var, inserted, term)) {
      return true;
    }
    return *inserted == term;
  }

  void specVar(unsigned var, TermList term) const
  {
    ASSERTION_VIOLATION;
  }

  void reset() {
    _map.reset();
  }

  bool bindsTerm = false;
  DHMap<unsigned,TermList> _map;
};

bool addConditions(VarOrderBV bits, ResultSubstitution* subst, bool result, VarOrderBV& res, const Ordering& ord)
{
  for (unsigned i = 0; i < 6; i++) {
    for (unsigned j = i+1; j <= 6; j++) {
      if (isBitSet(i,j,PoComp::GT,bits)) {
        auto xS = subst->applyTo(TermList(i,false),result);
        auto yS = subst->applyTo(TermList(j,false),result);
        VarOrderBV bits = getRemaining(res);
        if (!ord.isGreater(xS,yS,nullptr,&bits)) {
          res |= bits;
        } else {
          return true;
        }
      }
      if (isBitSet(i,j,PoComp::LT,bits)) {
        auto xS = subst->applyTo(TermList(i,false),result);
        auto yS = subst->applyTo(TermList(j,false),result);
        VarOrderBV bits = getRemaining(res);
        if (!ord.isGreater(yS,xS,nullptr,&bits)) {
          res |= bits;
        } else {
          return true;
        }
      }
      if (isBitSet(i,j,PoComp::EQ,bits)) {
        auto xS = subst->applyTo(TermList(i,false),result);
        auto yS = subst->applyTo(TermList(j,false),result);
        OneEqBinder binder;
        if (xS == yS) {
          return true;
        }
        if (MatchingUtils::matchTerms(xS,yS,binder)) {
          setBit(binder.b, binder.v, PoComp::EQ, res);
        }
      }
    }
  }
  return false;
}

// bool violatesCondition(const VarOrder& vo, ResultSubstitution* subst, bool result, const Ordering& ord, VarOrderBV& res)
// {
//   auto rit = vo.iter_relations();
//   while (rit.hasNext()) {
//     auto tp = rit.next();
//     auto x = get<0>(tp);
//     auto y = get<1>(tp);
//     auto c = get<2>(tp);
//     auto xS = subst->applyTo(TermList(x,false),result);
//     auto yS = subst->applyTo(TermList(y,false),result);
//     auto comp = ord.compare(xS,yS);
//     if (comp == Ordering::GREATER && (c == PoComp::EQ || c == PoComp::LT)) {
//       return true;
//     }
//     if (comp == Ordering::LESS && (c == PoComp::EQ || c == PoComp::GT)) {
//       return true;
//     }
//     if (comp == Ordering::EQUAL && (c == PoComp::GT || c == PoComp::LT)) {
//       return true;
//     }
//     VarOrderBV bits = getRemaining(res);
//     switch (c) {
//       case PoComp::GT: {
//         if (ord.isGreater(yS,xS,nullptr,&bits)) {
//           return true;
//         }
//         break;
//       }
//       case PoComp::LT: {
//         if (ord.isGreater(xS,yS,nullptr,&bits)) {
//           return true;
//         }
//         break;
//       }
//       case PoComp::EQ: {
//         if (ord.isGreater(yS,xS,nullptr,&bits)) {
//           return true;
//         }
//         VarOrderBV bits2 = getRemaining(bits);
//         if (ord.isGreater(yS,xS,nullptr,&bits2)) {
//           return true;
//         }
//         bits |= bits2;
//       }
//     }
//     if (bits) {
//       // cout << "remaining " << Int::toHexString(bits) << " from " << x << " " << xS << " " << toString(c) << " " << y << " " << yS << endl;
//       res |= bits;
//     }
//   }
//   return false;
// }

bool ReducibilityChecker::checkSupEager(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, bool eqClauseUnit)
{
  if (_opt.reducibilityCheck()!=Options::ReducibilityCheck::EAGER) {
    return false;
  }

  if (checkSup(rwLit, eqLit, eqLHS, rwTerm, rwTermS, tgtTermS, subst, eqIsResult, eqClauseUnit)) {
    return true;
  }

  // if (checkSupExpensive(rwLit, eqLit, eqLHS, rwTerm, rwTermS, tgtTermS, subst, eqIsResult, eqClauseUnit, nullptr)) {
  //   return true;
  // }
  return false;
}

bool ReducibilityChecker::checkInferenceLazy(Clause* cl)
{
  if (_opt.reducibilityCheck()!=Options::ReducibilityCheck::LAZY) {
    return false;
  }
  auto supInfo = cl->getSupInfo();
  if (!supInfo) {
    TIME_TRACE("no supinfo");
    return false;
  }
  reset();
  bool res = false;
  if (!supInfo->rwTerm) {
    TIME_TRACE("ReducibilityChecker::checkBRLazy");
    // BR
    ASS(supInfo->rwLit);
    res = checkBRExpensive(supInfo->rwLit);
  } else {
    RobSubstitution subst;
    subst.unify(supInfo->eqLHS, 0, TermList(supInfo->rwTerm), 1);
    auto rwTermS = subst.apply(TermList(supInfo->rwTerm), 1).term();
    auto tgtTerm = EqHelper::getOtherEqualitySide(supInfo->eqLit,supInfo->eqLHS);
    auto tgtTermS = subst.apply(tgtTerm, 0);
    auto rsubst = ResultSubstitution::fromSubstitution(&subst, 0, 1);
    // auto rwLitS = subst.apply(supInfo->rwLit, 1);
    // cout << "checking " << *cl << endl
    //      << *supInfo->rwLit << " " << *rwLitS << endl
    //      << *supInfo->rwTerm << " " << *rwTermS << endl
    //      << tgtTerm << " " << tgtTermS << endl
    //      << supInfo->eqLHS << endl
    //      << subst << endl << endl;

    // reset();

    res = checkSupExpensive(supInfo->rwLit, nullptr, supInfo->eqLHS, supInfo->rwTerm, rwTermS, tgtTermS,
      rsubst.ptr(), false, supInfo->eqClauseUnit, supInfo->splitSet);
    // cout << "non-redundant lazy" << endl;

    // reset();
    // if (checkSup(supInfo->rwLit, nullptr, supInfo->eqLHS, supInfo->rwTerm, rwTermS, tgtTermS,
    //   rsubst.ptr(), false, true))
    // {
    //   TIME_TRACE("cheap check");
    //   cout << "checking " << *cl << endl
    //       << *supInfo->rwLit << " " << *rwLitS << endl
    //       << *supInfo->rwTerm << " " << *rwTermS << endl
    //       << tgtTerm << " " << tgtTermS << endl
    //       << supInfo->eqLHS << endl
    //       << subst << endl
    //       << Int::toHexString(_reducedUnder) << endl
    //       << endl;
    //   return true;
    // }
  }
  // delete supInfo;
  cl->setSupInfo(nullptr);
  return res;
}

bool ReducibilityChecker::checkSup(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, bool eqClauseUnit)
{
  TIME_TRACE("ReducibilityChecker::checkSup");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  _ord.initStateForTerm(_rwTermState, rwTermS);
  // vstringstream exp;
  bool litIncomparable = false;
  if (pushSidesFromLiteral(rwLit, subst, !eqIsResult, rwTermS, litIncomparable)) {
    return true;
  }

  // {
  //   // calculate if substitution is renaming on rwTerm and the substitution itself
  //   Binder2 b;
  //   _substRenaming = MatchingUtils::matchTerms(TermList(rwTerm), TermList(rwTermS), b) && !b.bindsTerm;
  //   _subst.reset();
  //   if (!_substRenaming) {
  //     VariableIterator vit(rwTerm);
  //     _varmap = 0;
  //     while (vit.hasNext()) {
  //       auto v = vit.next();
  //       auto t = subst->apply(v,!eqIsResult);
  //       _subst.insert(v.var(),t);
  //       if (t.isTerm()) {
  //         _varmap |= (1 << v.var());
  //       }
  //     }
  //   }
  // }
  if (_sidesToCheck.size()==2) {
    TIME_TRACE("both sides skipped");
    return false;
  }

  if (litIncomparable) {
    VarOrderBV bits = getRemaining(_reducedUnder);
    NEVER(_ord.isGreater(tgtTermS,TermList(rwTermS),nullptr,&bits));
    _reducedUnder |= bits;
    if (isReducedUnderAny(_reducedUnder)) {
      return true;
    }
    OneEqBinder binder;
    if (MatchingUtils::matchTerms(TermList(rwTermS),tgtTermS,binder)) {
      setBit(binder.b, binder.v, PoComp::EQ, _reducedUnder);
    }
    if (isReducedUnderAny(_reducedUnder)) {
      return true;
    }
  }

  for (const auto& kv : _sidesToCheck) {
    TermList side = kv.first;
    Term* sideS = kv.second;

    // if (sideS->isLiteral()) {
    //   SLQueryResultIterator rit = _litIndex->getGeneralizations(static_cast<Literal*>(sideS), true, false);
    //   while (rit.hasNext()) {
    //     auto qr = rit.next();
    //     RobSubstitution rsubst;
    //     ALWAYS(rsubst.unifyArgs(qr.literal,0,rwLit,1));

    //     auto rwTermO = rsubst.apply(TermList(rwTerm),1);
    //     Binder b;
    //     if (MatchingUtils::matchTerms(rwTermO, TermList(rwTermS), b) && !b.renaming) {
    //       return true;
    //     }
    //   }
    // } else if (!_substRenaming) {
    //   VarOrderBV* ptr = _reducedLitCache.findPtr(make_pair(side.term(),rwLit));
    //   auto ptr2 = _reducedLitCache2.findPtr(make_pair(side.term(),rwLit));
    //   ASS(ptr);
    //   VarOrderBV test = 0;
    //   if (ptr2->isEmpty()) {
    //     TIME_TRACE("success by preprocess");
    //     return true;
    //   }/*  else {
    //     bool violatesAll = true;
    //     TIME_TRACE("violatesCondition check");
    //     for (const auto& vo : *ptr2) {
    //       VarOrderBV bits = 0;
    //       if (!violatesCondition(vo, subst, !eqIsResult, _ord, bits)) {
    //         violatesAll = false;
    //         // break;
    //       }
    //       test |= bits;
    //     }
    //     if (test) {
    //       cout << "test is " << Int::toHexString(test) << endl;
    //     }
    //     if (isReducedUnderAny(test)) {
    //       TIME_TRACE("reduced under any by new conditions");
    //       return true;
    //     }
    //     if (violatesAll) {
    //       TIME_TRACE("violatesConditions");
    //       return true;
    //     }
    //   } */
    //   if (isReducedUnderAny(*ptr)) {
    //     return true;
    //   }
    //   if (addConditions(*ptr, subst, !eqIsResult, test, _ord)) {
    //     return true;
    //   }
    //   _reducedUnder |= test;
    // }
    auto r = checkSide(side, sideS, rwTermS, &tgtTermS, /* exp, */ rwTerm, subst, !eqIsResult);
    // auto s = checkLiteralSanity(subst->apply(rwLit,!eqIsResult), rwTermS, exp);
    // if (s) {
    //   return true;
    // }
    // if (s != r) {
    //   USER_ERROR("x1 "+exp.str());
    // }
    if (r) {
      // if (isReducedUnderAny(_reducedUnder)) {
        // cout << "redundant1 " << *rwLit << " " << *eqLit << " " << eqLHS << endl;
      // }
      return true;
    }
  }

  LOG1(cout,"checking rwTerm");
  auto ptr = getCacheEntryForTerm(rwTermS);
  ASS(!argReduced(rwTermS));
  DHSet<pair<TermList,TermList>>::Iterator rIt(ptr->reducesTo);
  while (rIt.hasNext()) {
    auto kv = rIt.next();
    auto rhs = kv.first;
    // if (!eqClauseUnit) {
    //   return true;
    // }
    LOG2(cout,"rhs ",rhs.toString());
    VarOrderBV bits = getRemaining(_reducedUnder);
    if (!_ord.isGreater(tgtTermS,rhs,nullptr,&bits)) {
      LOG1(cout,"not greater tgtTerm");
      _reducedUnder |= bits;
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      continue;
    }
    return true;
  }

  DHMap<pair<TermList,TermList>,VarOrderBV>::Iterator rcIt(ptr->reducesToCond);
  while (rcIt.hasNext()) {
    pair<TermList,TermList> kv;
    VarOrderBV val;
    rcIt.next(kv,val);
    if (!eqClauseUnit) {
      _reducedUnder |= val;
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      continue;
    }
    auto rhs = kv.first;
    // Binder b;
    // if (MatchingUtils::matchTerms(kv.second,eqLHS,b) && !b.renaming) {
    //   _reducedUnder |= val;
    //   if (isReducedUnderAny(_reducedUnder)) {
    //     return true;
    //   }
    //   continue;
    // }
    LOG2(cout,"rhs ",rhs.toString());
    VarOrderBV bits = val & getRemaining(_reducedUnder);
    if (!_ord.isGreater(tgtTermS,rhs,nullptr,&bits)) {
      _reducedUnder |= bits;
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      continue;
    }
    _reducedUnder |= val;
    if (isReducedUnderAny(_reducedUnder)) {
      return true;
    }
  }
  if (isReducedUnderAny(_reducedUnder)) {
    return true;
  }
  if (isRemainingUnsat(_reducedUnder)) {
    return true;
  }
  return false;
}

bool ReducibilityChecker::checkBREager(Literal* lit)
{
  if (_opt.reducibilityCheck()!=Options::ReducibilityCheck::EAGER) {
    return false;
  }
  TIME_TRACE("ReducibilityChecker::checkBREager");
  ASS(!lit->isEquality());
  return checkSide(TermList(), lit, nullptr, nullptr, /* exp,  */nullptr, nullptr, false);
}

// bool ReducibilityChecker::checkLiteralSanity(Literal* lit, Term* rwTermS/*, vstringstream& exp*/)
// {
//   LOG2(exp,"check literal ",*lit);
//   LOG2(exp,"rwTermS ",*rwTermS);
//   Stack<Term*> toplevelTerms;
//   if (!lit->isEquality()) {
//     toplevelTerms.push(lit);
//   } else {
//     auto comp = _ord.getEqualityArgumentOrder(lit);
//     auto t0 = lit->termArg(0);
//     auto t1 = lit->termArg(1);
//     switch(comp) {
//       case Ordering::INCOMPARABLE:
//         if (t0.isTerm()) { toplevelTerms.push(t0.term()); }
//         if (t1.isTerm()) { toplevelTerms.push(t1.term()); }
//         break;
//       case Ordering::GREATER:
//       case Ordering::GREATER_EQ:
//         ASS(t0.isTerm());
//         toplevelTerms.push(t0.term());
//         break;
//       case Ordering::LESS:
//       case Ordering::LESS_EQ:
//         ASS(t1.isTerm());
//         toplevelTerms.push(t1.term());
//         break;
//       case Ordering::EQUAL:
//         if (lit->isPositive()) {
//           return true;
//         }
//         break;
//     }
//   }
//   DHSet<Term*> done;
//   for (Term* t : toplevelTerms) {
//     NonVariableNonTypeIterator stit(t, !t->isLiteral());
//     while (stit.hasNext()) {
//       auto st = stit.next();
//       if (!done.insert(st)) {
//         stit.right();
//         continue;
//       }
//       if (rwTermS && !_ord.isGreater(TermList(rwTermS),TermList(st))) {
//         continue;
//       }
//       auto it = _index->getGeneralizations(st,true);
//       while (it.hasNext()) {
//         auto qr = it.next();
//         TermList rhsS;
//         if (!getDemodulationRHSCodeTree(qr, st, rhsS)) {
//           continue;
//         }
//         if (!_ord.isGreater(TermList(st),rhsS)) {
//           continue;
//         }
//         LOG3(exp, *st, " => ", rhsS);
//         LOG4(exp, " in ", *t, " and ", *lit);
//         LOG2(exp, " is reducible by ", *qr.clause);
//         return true;
//       }
//     }
//   }
//   return false;
// }

// bool ReducibilityChecker::checkRwTermSanity(Term* rwTermS, TermList tgtTermS/*, vstringstream& exp*/)
// {
//   LOG2(exp,"check rwTerm ",*rwTermS);
//   auto it = _index->getGeneralizations(rwTermS,true);
//   while (it.hasNext()) {
//     auto qr = it.next();
//     TermList rhsS;
//     if (!getDemodulationRHSCodeTree(qr, rwTermS, rhsS)) {
//       continue;
//     }
//     if (_ord.compare(tgtTermS,rhsS) != Ordering::GREATER) {
//       continue;
//     }
//     if (_ord.compare(TermList(rwTermS),rhsS)!=Ordering::GREATER) {
//       continue;
//     }
//     LOG2(exp, "rwTermS ", *rwTermS);
//     LOG2(exp, "tgtTermS ", tgtTermS);
//     LOG2(exp, "rhsS ", rhsS);
//     LOG2(exp, "reducible by ", *qr.clause);
//     return true;
//   }
//   return false;
// }

bool ReducibilityChecker::getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS, SplitSet* ss)
{
  if (!qr.clause->noSplits() && !(ss && qr.clause->splits()->isSubsetOf(ss))) {
    return false;
  }
  if (qr.clause->rewritingData() && !qr.clause->rewritingData()->isEmpty()) {
    return false;
  }
  if (qr.clause->getSupInfo()) {
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
  if (_opt.reducibilityCheck()!=Options::ReducibilityCheck::EAGER) {
    return;
  }

  for (unsigned i = 0; i < cl->numSelected(); i++) {
    auto lit = (*cl)[i];
    if (!lit->isEquality()) {
      continue;
    }
    for (unsigned j = 0; j <= 1; j++) {
      auto side = *lit->nthArgument(j);
      if (side.isVar()) {
        continue;
      }

      auto argOrder = _ord.getEqualityArgumentOrder(lit);
      if ((j==0 && argOrder==Ordering::LESS) || (j==1 && argOrder==Ordering::GREATER)) {
        continue;
      }

      VarOrderBV* ptr;
      if (!_reducedLitCache.getValuePtr(make_pair(side.term(),lit),ptr,0)) {
        continue;
      }
      auto other = EqHelper::getOtherEqualitySide(lit, side);
      VarOrderBV bits = 0;
      NEVER(_ord.isGreater(other,side,nullptr,&bits));
      *ptr |= bits;

      NonVariableNonTypeIterator nvi(side.term(),false);
      while (nvi.hasNext()) {
        auto st = nvi.next();
        auto git = _index->getGeneralizations(st,true);
        while (git.hasNext()) {
          auto qr = git.next();
          TermList rhsS;
          if (!getDemodulationRHSCodeTree(qr, st, rhsS, nullptr)) {
            continue;
          }
          VarOrderBV bits = getRemaining(*ptr);
          NEVER(_ord.isGreater(TermList(st),rhsS,nullptr,&bits));
          *ptr |= bits;
        }
      }
      auto git = _index->getGeneralizations(side.term(),true);
      while (git.hasNext()) {
        auto qr = git.next();
        TermList rhsS;
        if (!getDemodulationRHSCodeTree(qr, side.term(), rhsS, nullptr)) {
          continue;
        }
        VarOrderBV bits = getRemaining(*ptr);
        if (!_ord.isGreater(side,rhsS,nullptr,&bits)) {
          VarOrderBV bits2 = bits;
          if (!_ord.isGreater(other,rhsS,nullptr,&bits2)) {
            *ptr |= bits2;
          } else {
            *ptr |= bits;
          }
        }
      }
    }
  }
  for (unsigned i = 0; i < cl->numSelected(); i++) {
    auto lit = (*cl)[i];
    if (!lit->isEquality()) {
      continue;
    }
    for (unsigned j = 0; j <= 1; j++) {
      auto side = *lit->nthArgument(j);
      if (side.isVar()) {
        continue;
      }
      auto other = EqHelper::getOtherEqualitySide(lit, side);
      auto argOrder = _ord.getEqualityArgumentOrder(lit);
      if ((j==0 && argOrder==Ordering::LESS) || (j==1 && argOrder==Ordering::GREATER)) {
        continue;
      }
      Stack<VarOrder>* rest;
      if (!_reducedLitCache2.getValuePtr(make_pair(side.term(),lit),rest)) {
        continue;
      }
      // rest->push(VarOrder());
      // continue;
      unsigned iterCnt = 0;
      Stack<VarOrder> vos;
      vos.push(VarOrder());
      while(vos.isNonEmpty()) {
        auto vo = vos.pop();
        if (iterCnt++>100) {
          rest->push(vo);
          continue;
        }
        VarOrder::EqApplicator voApp(vo);
        auto sideS = SubstHelper::apply(side,voApp);
        auto otherS = SubstHelper::apply(other,voApp);
        if (sideS == otherS) {
          continue;
        }
        VarOrder ext = vo;
        if (_ord.makeGreater(otherS,sideS,ext)) {
          for (const auto& nvo : VarOrder::order_diff(vo,ext)) {
            vos.push(nvo);
          }
          continue;
        }
        NonVariableNonTypeIterator nvi(sideS.term(),false);
        ClauseStack cls;
        while (nvi.hasNext()) {
          auto st = nvi.next();
          auto git = _index->getGeneralizations(st,true);
          while (git.hasNext()) {
            auto qr = git.next();
            TermList rhsS;
            if (!getDemodulationRHSCodeTree(qr, st, rhsS, nullptr)) {
              continue;
            }
            VarOrder ext = vo;
            if (_ord.makeGreater(TermList(st),rhsS,ext)) {
              for (const auto& nvo : VarOrder::order_diff(vo,ext)) {
                vos.push(nvo);
              }
              goto success_reduced;
            }
          }
        }
        {
          auto git = _index->getGeneralizations(sideS.term(),true);
          while (git.hasNext()) {
            auto qr = git.next();
            TermList rhsS;
            if (!getDemodulationRHSCodeTree(qr, sideS.term(), rhsS, nullptr)) {
              continue;
            }
            VarOrder ext = vo;
            if (_ord.makeGreater(sideS,rhsS,ext) && _ord.makeGreater(rhsS,otherS,ext)) {
              for (const auto& nvo : VarOrder::order_diff(vo,ext)) {
                vos.push(nvo);
              }
              goto success_reduced;
            }
          }
        }
        rest->push(vo);
success_reduced:
        continue;
      }
    }
  }

  if (cl->length()!=1 || !cl->noSplits()) {
    return;
  }
  LOG2(cout,"demodulator clause activated ",*cl);

  DHSet<Term*> changed;
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
      LOG2(cout,"possible cached term ",*t);
      LOG2(cout,"possible rhs ",rhsS);

      auto e = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
      VarOrderBV bits = getRemaining(t->reducesUnder());
      if (!_ord.isGreater(TermList(t),rhsS,nullptr,&bits)) {
        LOG1(cout,"not greater");
        t->reducesUnder() |= bits;
        VarOrderBV* ptr;
        e->reducesToCond.getValuePtr(make_pair(rhsS,lhs), ptr, 0);
        (*ptr) |= bits;
        changed.insert(t);
        continue;
      }
      LOG1(cout,"rhs reduces");
      ASS(!argReduced(t));
      e->reducesTo.insert(make_pair(rhsS,qr.term));
      t->markReduced();
      changed.insert(t);
    }
  }

  DHSet<Term*>::Iterator it(changed);
  while (it.hasNext()) {
    auto t = it.next();
    auto e = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
    for (const auto& st : e->superTerms) {
      if (argReduced(st)) {
        continue;
      }
      st->reducesUnder() |= t->reducesUnder();
      if (t->isReduced()) {
        st->markReduced();
        auto st_e = static_cast<ReducibilityEntry*>(st->reducibilityInfo());
        st_e->reducesTo.reset();
        _tis.remove(TypedTermList(st), static_cast<Literal*>(st), nullptr);
      }
      toUpdate.push(st);
    }
  }

  while (toUpdate.isNonEmpty()) {
    auto t = toUpdate.pop();
    auto e = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
    for (const auto& st : e->superTerms) {
      if (argReduced(st)) {
        continue;
      }
      st->reducesUnder() |= t->reducesUnder();
      if (t->isReduced()) {
        st->markReduced();
        auto st_e = static_cast<ReducibilityEntry*>(st->reducibilityInfo());
        st_e->reducesTo.reset();
        _tis.remove(TypedTermList(st), static_cast<Literal*>(st), nullptr);
      }
      toUpdate.push(st);
    }
  }
}

ReducibilityChecker::ReducibilityEntry* ReducibilityChecker::getCacheEntryForTerm(Term* t)
{
  auto e = static_cast<ReducibilityEntry*>(t->reducibilityInfo());
  // TIME_TRACE(e ? "ReducibilityChecker::getCacheEntryForTerm" : "ReducibilityChecker::getCacheEntryForTermFirst");
  if (e) {
    LOG2(cout,"cache exists ",*t);
#if VDEBUG
    if (!t->isReduced()) {
      NonVariableNonTypeIterator nvi(t);
      while (nvi.hasNext()) {
        auto st = nvi.next();
        ASS(!st->isReduced());
        ASS_REP(!(~t->reducesUnder() & st->reducesUnder()),t->toString()+" "+Int::toHexString(t->reducesUnder())+" "+st->toString()+" "+Int::toHexString(st->reducesUnder()));
      }
    }
#endif
    return e;
  }
  LOG2(cout,"cache term ",*t);
  e = new ReducibilityEntry();
  t->setReducibilityInfo(e);
  if (t->isReduced()) {
    return e;
  }
  for (unsigned i = t->numTypeArguments(); i < t->arity(); i++) {
    auto arg = t->nthArgument(i);
    if (arg->isVar()) {
      continue;
    }
    auto arg_e = getCacheEntryForTerm(arg->term());
    arg_e->superTerms.push(t);
    if (arg->term()->isReduced()) {
      LOG2(cout,"arg reduced ",*arg);
      t->markReduced();
      return e;
    }
    t->reducesUnder() |= arg->term()->reducesUnder();
  }

  auto it = _index->getGeneralizations(t,true);
  while (it.hasNext()) {
    auto qr = it.next();
    TermList rhsS;
    if (!getDemodulationRHSCodeTree(qr, t, rhsS, nullptr)) {
      continue;
    }
    LOG2(cout,"demodulator",*qr.clause);
    LOG2(cout,"rhs ",rhsS);
    Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
    VarOrderBV bits = getRemaining(0); // we query all bits here
    if (argOrder!=Ordering::LESS && argOrder!=Ordering::GREATER && !_ord.isGreater(TermList(t),rhsS,nullptr,&bits)) {
      t->reducesUnder() |= bits;
      VarOrderBV* ptr;
      e->reducesToCond.getValuePtr(make_pair(rhsS,qr.term), ptr, 0);
      (*ptr) |= bits;
      LOG1(cout,"not greater");
      continue;
    }

    t->markReduced();
    e->reducesTo.insert(make_pair(rhsS,qr.term));
  }
  if (!argReduced(t)) {
    LOG1(cout,"indexed");
    _tis.insert(TypedTermList(t), static_cast<Literal*>(t), nullptr);
  } else {
    LOG1(cout,"not indexed");
  }
  return e;
}

bool ReducibilityChecker::checkSide(TermList side, Term* sideS, Term* rwTermS, TermList* tgtTermS, /* vstringstream& exp,  */Term* rwTerm, ResultSubstitution* subst, bool result)
{
  ASS(side.isTerm());
  ASS(!rwTermS || sideS->containsSubterm(TermList(rwTermS)));
  DHSet<Term*> checked;
  // TODO where should we handle rwTerm?
  checked.insert(rwTermS);

  NonVariableNonTypeIterator stit(sideS, !sideS->isLiteral());
  while (stit.hasNext()) {
    auto st = stit.next();
    LOG2(cout,"checking subterm ",st->toString());
    if (!_attempted.insert(st)) {
      LOG1(cout,"already checked");
      stit.right();
      continue;
    }
    VarOrderBV bits = getRemaining(_reducedUnder);
    if (rwTermS && !_ord.isGreater(TermList(rwTermS),TermList(st),_rwTermState,&bits)) {
      if (!bits) {
        continue;
      }
      auto ptr = getCacheEntryForTerm(st);
      if (st->isReduced()) {
        _reducedUnder |= bits;
      } else {
        _reducedUnder |= (st->reducesUnder() & bits);
      }
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      LOG1(cout,"not greater");
      continue;
    }
    checked.insert(st);

    auto ptr = getCacheEntryForTerm(st);
    if (st->isReduced()) {
      LOG1(cout,"reduced");
      return true;
    }
    _reducedUnder |= st->reducesUnder();
    if (isReducedUnderAny(_reducedUnder)) {
      return true;
    }
    LOG1(cout,"not reduced");
    stit.right();
  }

  return false;
  if (!rwTerm || _substRenaming) {
    return false;
  }
  void* stSstate = _ord.createState();


  auto ft = FlatTerm::create(sideS);
  // FTNonTypeIterator stit(side,ft);
  // FTNonTypeIterator stit2(TermList(sideS),ft);
  CustomIterator cit(side,TermList(sideS),ft,checked);
  while (cit.hasNext()) {
    auto tp = cit.next();
    auto st = get<0>(tp);
    auto stS = get<1>(tp);
    auto e = get<2>(tp);
    if (st.term()->ground()) {
      cit.right();
      continue;
    }
    // if (!(st.term()->varmap() & rwTerm->varmap())) {
    //   stit.right();
    //   continue;
    // }
    ReducibilityEntry* ce = nullptr;
    // ReducibilityEntry* ce = getCacheEntryForTerm(stS.term());
    // ReducibilityEntry* ce = static_cast<ReducibilityChecker::ReducibilityEntry*>(stS.term()->reducibilityInfo());
    if (ce && !argReduced(stS.term())) {
      DHSet<pair<TermList,TermList>>::Iterator rIt(ce->reducesTo);
      while (rIt.hasNext()) {
        auto kv = rIt.next();
        RobSubstitution rsubst;
        ALWAYS(rsubst.unify(kv.second,0,st,1,nullptr,true));

        auto rwTermO = rsubst.apply(TermList(rwTerm),1);
        Binder b;
        if (MatchingUtils::matchTerms(rwTermO, TermList(rwTermS), b) && !b.renaming) {
          return true;
        }
      }
      DHMap<pair<TermList,TermList>,VarOrderBV>::Iterator rcIt(ce->reducesToCond);
      while (rcIt.hasNext()) {
        pair<TermList,TermList> kv;
        VarOrderBV val;
        rcIt.next(kv,val);
        Binder b;
        if (MatchingUtils::matchTerms(kv.second,st,b) && !b.renaming) {
          _reducedUnder |= val;
          if (isReducedUnderAny(_reducedUnder)) {
            return true;
          }
        }
      }
    } else {
      _ord.initStateForTerm(stSstate,stS.term());
      auto git = _index->getGeneralizations(stS.term(), true, e);
      while (git.hasNext()) {
        auto qr = git.next();
        if (!qr.clause->noSplits()) {
          continue;
        }
        if (qr.clause->getSupInfo()) {
          continue;
        }
        {static RobSubstitution subst;
        TypedTermList trm(stS.term());
        bool resultTermIsVar = qr.term.isVar();
        if (resultTermIsVar) {
          TermList querySort = trm.sort();
          TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
          subst.reset();
          if (!subst.match(eqSort, 0, querySort, 1)) {
            continue;
          }
        }}
        TermList rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
        Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
        bool oriented = true;
        VarOrderBV bits = getRemaining(_reducedUnder);
        // TODO !!!!!!!!! enable constraints below
        // auto rhsS = qr.substitution->applyToBoundResult(rhs);
        // if (argOrder!=Ordering::LESS && argOrder!=Ordering::GREATER && !_ord.isGreater(TermList(stS),rhsS,stSstate,&bits)) {
        if (argOrder!=Ordering::LESS && argOrder!=Ordering::GREATER && !_ord.isGreater(TermList(stS),rhs,stSstate,&bits,&qr)) {
          oriented = false;
        }
        if (!oriented && !bits) {
          continue;
        }
        if (_varmap & ~st.term()->varmap()) {
          if (oriented) {
            return true;
          }
          _reducedUnder |= bits;
          if (isReducedUnderAny(_reducedUnder)) {
            return true;
          }
          continue;
        }
        static RobSubstitution rsubst;
        rsubst.reset();
        ALWAYS(rsubst.unify(st,0,qr.term,1,nullptr,true));

        Binder b;
        DHMap<unsigned,TermList>::Iterator rwvIt(_subst);
        while (rwvIt.hasNext()) {
          unsigned v;
          TermList right;
          rwvIt.next(v,right);
          auto left = rsubst.apply(TermList(v,false),0,true);
          if (left.weight()<right.weight()) {
            if (oriented) {
              return true;
            }
            _reducedUnder |= bits;
            if (isReducedUnderAny(_reducedUnder)) {
              return true;
            }
            break;
          }
          ALWAYS(MatchingUtils::matchTerms(left, right, b));
          if (b.renaming) {
            continue;
          }
          if (oriented) {
            return true;
          }
          _reducedUnder |= bits;
          if (isReducedUnderAny(_reducedUnder)) {
            return true;
          }
          break;
        }
      }
    }
  }
  ft->destroy();
  _ord.destroyState(stSstate);

  return false;
}

bool ReducibilityChecker::checkSupExpensive(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, bool eqClauseUnit, SplitSet* rwSplitSet)
{
  TIME_TRACE("ReducibilityChecker::checkSupExpensive");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  _ord.initStateForTerm(_rwTermState, rwTermS);
  // vstringstream exp;
  bool litIncomparable = false;
  if (pushSidesFromLiteral(rwLit, subst, !eqIsResult, rwTermS, litIncomparable)) {
    return true;
  }

  {
    // calculate if substitution is renaming on rwTerm and the substitution itself
    Binder b;
    _substRenaming = MatchingUtils::matchTerms(TermList(rwTerm), TermList(rwTermS), b) && b.renaming;
    _subst.reset();
    if (!_substRenaming) {
      VariableIterator vit(rwTerm);
      _varmap = 0;
      while (vit.hasNext()) {
        auto v = vit.next();
        auto t = subst->apply(v,!eqIsResult);
        _subst.insert(v.var(),t);
        if (t.isTerm()) {
          _varmap |= (1 << v.var());
        }
      }
    }
  }
  if (_sidesToCheck.size()==2) {
    TIME_TRACE("both sides skipped");
    return false;
  }

  // cout << 3 << endl;
  for (const auto& kv : _sidesToCheck) {
    TermList side = kv.first;
    Term* sideS = kv.second;

    Stack<VarOrder> todo;
    todo.push(VarOrder());
    // unsigned iterCnt = 0;
    while (todo.isNonEmpty()) {
      auto vo = todo.pop();
      // iterCnt++;
      VarOrder::EqApplicator voApp(vo);
      auto rwTermSS = SubstHelper::apply(rwTermS, voApp);
      auto tgtTermSS = SubstHelper::apply(tgtTermS, voApp);
      auto sideSS = SubstHelper::apply(sideS, voApp);
      if (tgtTermSS == TermList(rwTermSS) || _ord.isGreater(tgtTermSS,TermList(rwTermSS),vo)) {
        // cout << "redundant under " << vo.to_string() << endl;
        // the superposition itself is redundant, skip this order
        continue;
      }

      EqBinder eb;
      eb.vo = vo;
      if (MatchingUtils::matchTerms(TermList(rwTermSS),tgtTermSS,eb)) {
        auto vos = VarOrder::order_diff(vo,eb.vo);
        for (auto&& evo : vos) {
          todo.push(std::move(evo));
        }
        continue;
      }

      VarOrder ext = vo;
      if (_ord.makeGreater(tgtTermSS,TermList(rwTermSS),ext)) {
        auto vos = VarOrder::order_diff(vo,ext);
        for (auto&& evo : vos) {
          todo.push(std::move(evo));
        }
        continue;
      }

      if (litIncomparable) {
        eb.vo = vo;
        auto other = EqHelper::getOtherEqualitySide(rwLit,side);
        auto otherS = subst->apply(other,!eqIsResult);
        auto otherSS = SubstHelper::apply(otherS,voApp);
        if (MatchingUtils::matchTerms(otherSS,TermList(sideSS),eb)) {
          auto vos = VarOrder::order_diff(vo,eb.vo);
          for (auto&& evo : vos) {
            todo.push(std::move(evo));
          }
          continue;
        }

        VarOrder ext = vo;
        if (_ord.makeGreater(otherSS,TermList(sideSS),ext)) {
          auto vos = VarOrder::order_diff(vo,ext);
          for (auto&& evo : vos) {
            todo.push(std::move(evo));
          }
          continue;
        }
      }

      DHSet<Term*> attempted;

      // try subterms of rwTermSS
      // NonVariableNonTypeIterator stit(rwTermSS);
      // while (stit.hasNext()) {
      //   auto st = stit.next();
      //   if (!attempted.insert(st)) {
      //     stit.right();
      //     continue;
      //   }

      //   auto it = _index->getGeneralizations(st,true);
      //   while (it.hasNext()) {
      //     auto qr = it.next();
      //     TermList rhsS;
      //     if (!getDemodulationRHSCodeTree(qr, st, rhsS, rwSplitSet)) {
      //       continue;
      //     }
      //     VarOrder ext = vo;
      //     if (!_ord.makeGreater(TermList(st),rhsS,ext)) {
      //       continue;
      //     }
      //     // cout << "redundant under " << vo.to_string() << " by " << *qr.clause << endl;
      //     if (!qr.clause->noSplits()) {
      //       TIME_TRACE("reduced by clause with splits");
      //     }
      //     auto vos = VarOrder::order_diff(vo,ext);
      //     for (auto&& evo : vos) {
      //       todo.push(std::move(evo));
      //     }
      //     goto loop_end;
      //   }
      // }

      {
        NonVariableNonTypeIterator stit(side.term(), !side.term()->isLiteral());
        while (stit.hasNext()) {
          auto st = stit.next();
          auto stS = subst->apply(TermList(st),!eqIsResult);
          auto stSS = SubstHelper::apply(stS.term(), voApp);
          if (!attempted.insert(stSS)) {
            stit.right();
            continue;
          }
          VarOrder ext = vo;
          bool rwTermGreater = rwTermSS->isLiteral() || _ord.makeGreater(TermList(rwTermSS),TermList(stSS),ext);
          // TODO is this needed?
          if (stSS!=rwTermSS && stSS->containsSubterm(TermList(rwTermSS))) {
            continue;
          }

          auto it = _index->getGeneralizations(stSS,true);
          while (it.hasNext()) {
            auto qr = it.next();
            TermList rhsS;
            if (!getDemodulationRHSCodeTree(qr, stSS, rhsS, rwSplitSet)) {
              continue;
            }

            bool moreGeneral = false;
            {
              static RobSubstitution rsubst;
              rsubst.reset();
              ALWAYS(rsubst.unify(TermList(st),0,qr.term,1,nullptr,true));

              Binder b;
              DHMap<unsigned,TermList>::Iterator rwvIt(_subst);
              while (rwvIt.hasNext()) {
                unsigned v;
                TermList right;
                rwvIt.next(v,right);
                // auto rightSS = SubstHelper::apply(right, voApp);
                auto left = rsubst.apply(TermList(v,false),0,true);
                if (!MatchingUtils::matchTerms(left, right, b)) {
                  // this can happen when x=y for some variables
                  break;
                }
                if (b.renaming) {
                  continue;
                }
                moreGeneral = true;
                break;
              }
            }
            if (!rwTermGreater && !moreGeneral) {
              continue;
            }
            VarOrder ext2 = moreGeneral ? vo : ext;
            if (!_ord.makeGreater(TermList(stSS),rhsS,ext2)) {
              continue;
            }
            if (TermList(st) == side && rwLit->isEquality() && rwLit->isPositive()) {
              auto other = EqHelper::getOtherEqualitySide(rwLit,side);
              auto otherS = subst->apply(other,!eqIsResult);
              auto otherSS = SubstHelper::apply(otherS,voApp);
              if (!_ord.makeGreater(otherSS,rhsS,ext2)) {
                continue;
              }
            }
            // if (!qr.clause->noSplits()) {
            //   TIME_TRACE("reduced by clause with splits");
            // }
            // {
            //   RobSubstitution tempSubst;
            //   if (tempSubst.match(qr.term, 0, stS, 1)) {
            //     // cout << "match" << endl;
            //     auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
            //     auto stSR = tempSubst.apply(stS,1);
            //     auto rhsS = tempSubst.apply(rhs,0);
            //     // cout << "stS " << stS << " rhsS " << rhsS << endl;
            //     if (_ord.compare(stSR,rhsS)==Ordering::GREATER) {
            //       TIME_TRACE("st reduces unconditionally");
            //       /* _ord.compare(TermList(rwTermS),stS)==Ordering::GREATER &&  */
            //       continue;
            //     } else {
            //       ASS(!ext2.is_empty());
            //     }
            //   }
            // }
            // if (ext2.is_empty()) {
            //   cout << "redundant2 under " << vo.to_string() << " by " << *qr.clause << " " << qr.term << endl;
            //   cout << *st << " " << stS << " " << *stSS << endl;
            // }
            auto vos = VarOrder::order_diff(vo,ext2);
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
          TermList rhsS;
          if (!getDemodulationRHSCodeTree(qr, rwTermSS, rhsS, rwSplitSet)) {
            continue;
          }
          VarOrder ext = vo;
          if (!_ord.makeGreater(tgtTermSS,rhsS,ext)) {
            continue;
          }
          if (!_ord.makeGreater(TermList(rwTermSS),rhsS,ext)) {
            continue;
          }
          // if (!qr.clause->noSplits()) {
          //   TIME_TRACE("reduced by clause with splits");
          // }
          // {
          //   RobSubstitution tempSubst;
          //   if (tempSubst.match(qr.term, 0, TermList(rwTermS), 1)) {
          //     auto rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
          //     auto rwTermSR = tempSubst.apply(TermList(rwTermS),1);
          //     auto rhsS = tempSubst.apply(rhs,0);
          //     if (_ord.compare(TermList(rwTermSR),rhsS)==Ordering::GREATER && _ord.compare(tgtTermS,rhsS)==Ordering::GREATER) {
          //       TIME_TRACE("rwterm reduces unconditionally");
          //       continue;
          //     }
          //   }
          // }
          // if (ext.is_empty()) {
          // cout << "redundant3 under " << vo.to_string() << " by " << *qr.clause << endl;
          // }
          auto vos = VarOrder::order_diff(vo,ext);
          for (auto&& evo : vos) {
            todo.push(std::move(evo));
          }
          goto loop_end;
        }
      }

      // could not reduce under this partial extension
      // cout << "fail " << iterCnt << endl;
      return false;
  loop_end:
      // if (vo.is_empty() && todo.isEmpty()) {
      //   cout << "here" << endl;
      // }
      continue;
    }
    // cout << "success " << iterCnt << endl;
    // if (iterCnt==1) {
    //   TIME_TRACE("reduced under {}");
    //   return false;
    // }
  }
  return true;
}

bool ReducibilityChecker::checkBRExpensive(Literal* rwLit)
{
  TIME_TRACE("ReducibilityChecker::checkBRExpensive");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  ASS(!rwLit->isEquality());

  Stack<VarOrder> todo;
  todo.push(VarOrder());
  // unsigned iterCnt = 0;
  while (todo.isNonEmpty()) {
    auto vo = todo.pop();
    // iterCnt++;
    VarOrder::EqApplicator voApp(vo);
    auto rwLitSS = SubstHelper::apply(rwLit, voApp);
    DHSet<Term*> attempted;

    NonVariableNonTypeIterator stit(rwLitSS);
    while (stit.hasNext()) {
      auto st = stit.next();
      if (!attempted.insert(st)) {
        stit.right();
        continue;
      }

      auto it = _index->getGeneralizations(st,true);
      while (it.hasNext()) {
        auto qr = it.next();
        TermList rhsS;
        if (!getDemodulationRHSCodeTree(qr, st, rhsS, nullptr)) {
          continue;
        }
        VarOrder ext = vo;
        if (!_ord.makeGreater(TermList(st),rhsS,ext)) {
          continue;
        }
        // cout << "redundant under " << vo.to_string() << " by " << *qr.clause << endl;
        auto vos = VarOrder::order_diff(vo,ext);
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

}