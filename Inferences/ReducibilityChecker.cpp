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
#include "Kernel/FlatTerm.hpp"
#include "Kernel/Matcher.hpp"
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

bool ReducibilityChecker::pushSidesFromLiteral(Literal* lit, ResultSubstitution* subst, bool result, Term* rwTermS)
{
  _sidesToCheck.reset();
  _sidesToCheck2.reset();

  if (!lit->isEquality()) {
    _sidesToCheck.push(subst->apply(lit,result));
    _sidesToCheck2.push(TermList(lit));
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
            _sidesToCheck.push(t0s.term());
            _sidesToCheck2.push(t0);
          }
          if (t1s.isTerm() && t1s.containsSubterm(TermList(rwTermS))) {
            _sidesToCheck.push(t1s.term());
            _sidesToCheck2.push(t1);
          }
          break;
        case Ordering::GREATER:
        case Ordering::GREATER_EQ:
          if (t0s.isTerm()) {
            ASS(t0s.containsSubterm(TermList(rwTermS)));
            _sidesToCheck.push(t0s.term());
            _sidesToCheck2.push(t0);
          }
          break;
        case Ordering::LESS:
        case Ordering::LESS_EQ:
          if (t1s.isTerm()) {
            ASS(t1s.containsSubterm(TermList(rwTermS)));
            _sidesToCheck.push(t1s.term());
            _sidesToCheck2.push(t1);
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
      _sidesToCheck.push(t0s.term());
      _sidesToCheck2.push(t0);
      break;
    }
    case Ordering::LESS:
    case Ordering::LESS_EQ: {
      ASS(t1.isTerm());
      auto t1s = subst->apply(t1,result);
      ASS(t1s.containsSubterm(TermList(rwTermS)));
      _sidesToCheck.push(t1s.term());
      _sidesToCheck2.push(t1);
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

bool violatesCondition(const VarOrder& vo, ResultSubstitution* subst, bool result, const Ordering& ord)
{
  auto rit = vo.iter_relations();
  while (rit.hasNext()) {
    auto tp = rit.next();
    auto x = get<0>(tp);
    auto y = get<1>(tp);
    auto c = get<2>(tp);
    auto xS = subst->applyTo(TermList(x,false),result);
    auto yS = subst->applyTo(TermList(y,false),result);
    auto comp = ord.compare(xS,yS);
    if (comp == Ordering::GREATER && (c == PoComp::EQ || c == PoComp::LT)) {
      return true;
    }
    if (comp == Ordering::LESS && (c == PoComp::EQ || c == PoComp::GT)) {
      return true;
    }
    if (comp == Ordering::EQUAL && (c == PoComp::GT || c == PoComp::LT)) {
      return true;
    }
  }
  return false;
}

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

bool ReducibilityChecker::checkSup(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, Ordering::Result rwComp, bool eqClauseUnit)
{
  TIME_TRACE("ReducibilityChecker::checkSup");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  _ord.initStateForTerm(_rwTermState, rwTermS);
  // vstringstream exp;
  if (pushSidesFromLiteral(rwLit, subst, !eqIsResult, rwTermS)) {
    return true;
  }

  {
    Binder b;
    if (MatchingUtils::matchTerms(TermList(rwTerm), TermList(rwTermS), b) && !b.renaming) {
      VarOrderBV* ptr = nullptr;
      if (_sidesToCheck2.size()==1) {
        ptr = _reducedLitCache.findPtr(make_pair(_sidesToCheck2[0].term(),rwLit));
      } else if (_sidesToCheck2.size()==2) {
        if (!_sidesToCheck2[0].containsSubterm(TermList(rwTerm))) {
          ptr = _reducedLitCache.findPtr(make_pair(_sidesToCheck2[1].term(),rwLit));
        }
        if (!_sidesToCheck2[1].containsSubterm(TermList(rwTerm))) {
          ptr = _reducedLitCache.findPtr(make_pair(_sidesToCheck2[0].term(),rwLit));
        }
      }
      if (ptr) {
        VarOrderBV test = 0;
        if (addConditions(*ptr, subst, !eqIsResult, test, _ord)) {
          TIME_TRACE("reduced");
          return true;
        }
        _reducedUnder |= test;
      }
    }
  }
  if (rwLit->isEquality()) {
    if (_sidesToCheck.size()==2) {
      OneEqBinder binder;
      if (MatchingUtils::matchTerms(TermList(_sidesToCheck[0]),TermList(_sidesToCheck[1]),binder)) {
        setBit(binder.b, binder.v, PoComp::EQ, _reducedUnder);
      }
    }
  }
  auto r = checkLiteral(rwTermS, &tgtTermS, /* exp, */ rwTerm, subst, !eqIsResult);
  // auto s = checkLiteralSanity(subst->apply(rwLit,!eqIsResult), rwTermS, exp);
  // if (s) {
  //   return true;
  // }
  // if (s != r) {
  //   USER_ERROR("x1 "+exp.str());
  // }
  if (r) {
    return true;
  }

  if (!rwLit->isEquality()) {
    SLQueryResultIterator rit = _litIndex->getGeneralizations(static_cast<Literal*>(_sidesToCheck[0]), true, false);
    while (rit.hasNext()) {
      auto qr = rit.next();
      RobSubstitution rsubst;
      ALWAYS(rsubst.unifyArgs(qr.literal,0,rwLit,1));

      auto rwTermO = rsubst.apply(TermList(rwTerm),1);
      Binder b;
      if (MatchingUtils::matchTerms(rwTermO, TermList(rwTermS), b) && !b.renaming) {
        TIME_TRACE("this check BR");
        return true;
      }
    }
  }

  LOG1(exp,"checking rwTerm");
  auto ptr = getCacheEntryForTerm(rwTermS);
  ASS_REP(!argReduced(rwTermS),rwTermS->toString()+" "+subst->apply(rwLit,!eqIsResult)->toString()+" "+Int::toString(_sidesToCheck.size())+" "+_sidesToCheck[0]->toString());
  DHSet<pair<TermList,Term*>>::Iterator rIt(ptr->reducesTo);
  while (rIt.hasNext()) {
    auto kv = rIt.next();
    auto rhs = kv.first;
    if (!eqClauseUnit) {
      return true;
    }
    LOG2(exp,"rhs ",rhs.toString());
    VarOrderBV bits = getRemaining(_reducedUnder);
    if (!_ord.isGreater(tgtTermS,rhs,nullptr,&bits)) {
      LOG1(exp,"not greater tgtTerm");
      _reducedUnder |= bits;
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      continue;
    }
    return true;
  }

  DHMap<pair<TermList,Term*>,VarOrderBV>::Iterator rcIt(ptr->reducesToCond);
  while (rcIt.hasNext()) {
    pair<TermList,Term*> kv;
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
    auto lhsO = kv.second;
    Binder b;
    if (MatchingUtils::matchTerms(TermList(lhsO),eqLHS,b) && !b.renaming) {
      _reducedUnder |= val;
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      continue;
    }
    LOG2(exp,"rhs ",rhs.toString());
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
  auto temp = _reducedUnder;
  if (rwComp==Ordering::INCOMPARABLE) {
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
  if (temp != _reducedUnder) {
    TIME_TRACE("eq is redundant under");
  }
  if (isRemainingUnsat(_reducedUnder)) {
    TIME_TRACE("remaining unsat");
    return true;
  }
  return false;
}

bool ReducibilityChecker::checkLiteral(Literal* lit)
{
  TIME_TRACE("ReducibilityChecker::checkLiteral");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  switch (_opt.reducibilityCheck()) {
    case Options::ReducibilityCheck::SMALLER: {
      // vstringstream exp;
      _sidesToCheck.reset();
      if (!lit->isEquality()) {
        _sidesToCheck.push(lit);
      } else {
        auto comp = _ord.getEqualityArgumentOrder(lit);
        auto t0 = lit->termArg(0);
        auto t1 = lit->termArg(1);
        switch(comp) {
          case Ordering::INCOMPARABLE:
            if (t0.isTerm()) { _sidesToCheck.push(t0.term()); }
            if (t1.isTerm()) { _sidesToCheck.push(t1.term()); }
            break;
          case Ordering::GREATER:
          case Ordering::GREATER_EQ:
            ASS(t0.isTerm());
            _sidesToCheck.push(t0.term());
            break;
          case Ordering::LESS:
          case Ordering::LESS_EQ:
            ASS(t1.isTerm());
            _sidesToCheck.push(t1.term());
            break;
          case Ordering::EQUAL:
            if (lit->isPositive()) {
              return true;
            }
            break;
        }
      }
      auto res = checkLiteral(nullptr, nullptr, /* exp,  */nullptr, nullptr, false);
      // auto res2 = checkLiteralSanity(lit, nullptr, nullptr, exp);
      // if (res != res2) {
      //   USER_ERROR("Sanity failed "+exp.str());
      // }
      return res;
    }
    case Options::ReducibilityCheck::SMALLER_GROUND: {
      // vstringstream exp;
      // return checkSmallerGround3(lits, nullptr, nullptr, exp);
      // // return checkSmallerGround2(lits, nullptr, nullptr, exp);
      // // return checkSmallerGround(lits, nullptr, nullptr, exp);
    }
    default:
      return false;
  }
  ASSERTION_VIOLATION;
}

bool ReducibilityChecker::checkLiteralSanity(Literal* lit, Term* rwTermS/*, vstringstream& exp*/)
{
  LOG2(exp,"check literal ",*lit);
  LOG2(exp,"rwTermS ",*rwTermS);
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
    }
  }
  DHSet<Term*> done;
  for (Term* t : toplevelTerms) {
    NonVariableNonTypeIterator stit(t, !t->isLiteral());
    while (stit.hasNext()) {
      auto st = stit.next();
      if (!done.insert(st)) {
        stit.right();
        continue;
      }
      if (rwTermS && !_ord.isGreater(TermList(rwTermS),TermList(st))) {
        continue;
      }
      auto it = _index->getGeneralizations(st,true);
      while (it.hasNext()) {
        auto qr = it.next();
        TermList rhsS;
        if (!getDemodulationRHSCodeTree(qr, st, rhsS)) {
          continue;
        }
        if (!_ord.isGreater(TermList(st),rhsS)) {
          continue;
        }
        LOG3(exp, *st, " => ", rhsS);
        LOG4(exp, " in ", *t, " and ", *lit);
        LOG2(exp, " is reducible by ", *qr.clause);
        return true;
      }
    }
  }
  return false;
}

bool ReducibilityChecker::checkRwTermSanity(Term* rwTermS, TermList tgtTermS/*, vstringstream& exp*/)
{
  LOG2(exp,"check rwTerm ",*rwTermS);
  auto it = _index->getGeneralizations(rwTermS,true);
  while (it.hasNext()) {
    auto qr = it.next();
    TermList rhsS;
    if (!getDemodulationRHSCodeTree(qr, rwTermS, rhsS)) {
      continue;
    }
    if (_ord.compare(tgtTermS,rhsS) != Ordering::GREATER) {
      continue;
    }
    if (_ord.compare(TermList(rwTermS),rhsS)!=Ordering::GREATER) {
      continue;
    }
    LOG2(exp, "rwTermS ", *rwTermS);
    LOG2(exp, "tgtTermS ", tgtTermS);
    LOG2(exp, "rhsS ", rhsS);
    LOG2(exp, "reducible by ", *qr.clause);
    return true;
  }
  return false;
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

      VarOrderBV* ptr;
      if (!_reducedLitCache.getValuePtr(make_pair(side.term(),lit),ptr,0)) {
        continue;
      }
      NonVariableNonTypeIterator nvi(side.term(),false);
      while (nvi.hasNext()) {
        auto st = nvi.next();
        auto git = _index->getGeneralizations(st,true);
        while (git.hasNext()) {
          auto qr = git.next();
          TermList rhsS;
          if (!getDemodulationRHSCodeTree(qr, st, rhsS)) {
            continue;
          }
          Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
          VarOrderBV bits = getRemaining(*ptr);
          NEVER(_ord.isGreater(TermList(st),rhsS,nullptr,&bits));
          *ptr |= bits;
        }
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
        e->reducesToCond.getValuePtr(make_pair(rhsS,lhs.term()), ptr, 0);
        (*ptr) |= bits;
        changed.insert(t);
        continue;
      }
      LOG1(cout,"rhs reduces");
      ASS(!argReduced(t));
      e->reducesTo.insert(make_pair(rhsS,qr.term.term()));
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
    if (!getDemodulationRHSCodeTree(qr, t, rhsS)) {
      continue;
    }
    LOG2(cout,"rhs ",rhsS);
    Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
    VarOrderBV bits = getRemaining(0); // we query all bits here
    if (argOrder!=Ordering::LESS && argOrder!=Ordering::GREATER && !_ord.isGreater(TermList(t),rhsS,nullptr,&bits)) {
      t->reducesUnder() |= bits;
      VarOrderBV* ptr;
      e->reducesToCond.getValuePtr(make_pair(rhsS,qr.term.term()), ptr, 0);
      (*ptr) |= bits;
      LOG1(cout,"not greater");
      continue;
    }

    t->markReduced();
    e->reducesTo.insert(make_pair(rhsS,qr.term.term()));
  }
  if (!argReduced(t)) {
    LOG1(cout,"indexed");
    _tis.insert(TypedTermList(t), static_cast<Literal*>(t), nullptr);
  } else {
    LOG1(cout,"not indexed");
  }
  return e;
}

bool ReducibilityChecker::checkLiteral(Term* rwTermS, TermList* tgtTermS, /* vstringstream& exp,  */Term* rwTerm, ResultSubstitution* subst, bool result)
{
  ASS(_sidesToCheck.isNonEmpty());
  DHSet<Term*> checked;
  // TODO where should we handle rwTerm?
  checked.insert(rwTermS);

  for (Term* side : _sidesToCheck) {
    ASS(side->containsSubterm(TermList(rwTermS)));

    NonVariableNonTypeIterator stit(side, !side->isLiteral());
    while (stit.hasNext()) {
      auto st = stit.next();
      LOG2(exp,"checking subterm ",st->toString());
      if (!_attempted.insert(st)) {
        LOG1(exp,"already checked");
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
        LOG1(exp,"not greater");
        continue;
      }
      checked.insert(st);

      auto ptr = getCacheEntryForTerm(st);
      if (st->isReduced()) {
        LOG1(exp,"reduced");
        return true;
      }
      _reducedUnder |= st->reducesUnder();
      if (isReducedUnderAny(_reducedUnder)) {
        return true;
      }
      LOG1(exp,"not reduced");
      stit.right();
    }
  }

  // return false;
  if (!rwTerm) {
    return false;
  }
  Binder b;
  if (MatchingUtils::matchTerms(TermList(rwTerm), TermList(rwTermS), b) && b.renaming) {
    TIME_TRACE("sup renaming on rwterm");
    return false;
  }
  DHMap<unsigned,TermList> rwTermVars;
  VariableIterator vit(rwTerm);
  unsigned varmap = 0;
  while (vit.hasNext()) {
    auto v = vit.next();
    auto t = subst->apply(v,result);
    rwTermVars.insert(v.var(),t);
    if (t.isTerm()) {
      varmap |= (1 << v.var());
    }
  }
  void* stSstate = _ord.createState();
  ASS(_sidesToCheck.size()==_sidesToCheck2.size());
  for (unsigned i = 0; i < _sidesToCheck.size(); i++) {
    auto sideS = _sidesToCheck[i];
    auto side = _sidesToCheck2[i];

    if (side.isVar()) {
      continue;
    }
    ASS(sideS->containsSubterm(TermList(rwTermS)));

    auto ft = FlatTerm::create(sideS);
    // FTNonTypeIterator stit(side,ft);
    // FTNonTypeIterator stit2(TermList(sideS),ft);
    CustomIterator stit(side,TermList(sideS),ft,checked);
    while (stit.hasNext()) {
      auto tp = stit.next();
      auto st = get<0>(tp);
      auto stS = get<1>(tp);
      auto e = get<2>(tp);
      if (st.term()->ground()) {
        stit.right();
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
        DHSet<pair<TermList,Term*>>::Iterator rIt(ce->reducesTo);
        while (rIt.hasNext()) {
          auto kv = rIt.next();
          RobSubstitution rsubst;
          ALWAYS(rsubst.unify(TermList(kv.second),0,st,1,nullptr,true));

          auto rwTermO = rsubst.apply(TermList(rwTerm),1);
          Binder b;
          if (MatchingUtils::matchTerms(rwTermO, TermList(rwTermS), b) && !b.renaming) {
            return true;
          }
        }
        DHMap<pair<TermList,Term*>,VarOrderBV>::Iterator rcIt(ce->reducesToCond);
        while (rcIt.hasNext()) {
          pair<TermList,Term*> kv;
          VarOrderBV val;
          rcIt.next(kv,val);
          auto lhsO = kv.second;
          Binder b;
          if (MatchingUtils::matchTerms(TermList(lhsO),st,b) && !b.renaming) {
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
          if (varmap & ~st.term()->varmap()) {
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
          DHMap<unsigned,TermList>::Iterator rwvIt(rwTermVars);
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
  }
  _ord.destroyState(stSstate);

  return false;
}

}