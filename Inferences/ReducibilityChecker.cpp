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
  unsigned taArity; 
  unsigned arity;

  if(t->isLiteral() && static_cast<Literal*>(t)->isEquality()){
    taArity = 0;
    arity = 2;
  } else {
    taArity = sym->numTypeArguments();
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

void setBits(unsigned x, unsigned y, PoComp c, uint64_t& val)
{
  if (x > y) {
    swap(x,y);
    c = reverse(c);
  }
  size_t idx = y*(y-1)/2 + x;
  size_t pos;
  switch (c) {
    case PoComp::GT:
      pos = 3*idx;
      break;
    case PoComp::EQ:
      pos = 3*idx+1;
      break;
    case PoComp::LT:
      pos = 3*idx+2;
      break;
    case PoComp::INC:
      ASSERTION_VIOLATION;
  }
  val |= 1UL << pos;
}

// ~000 & 111 -> 111 & 111 -> 1
// ~001 & 111 -> 110 & 111 -> 1
// ...
// ~111 & 111 -> 000 & 111 -> 0

bool isReducedUnderAny(uint64_t val)
{
  for (unsigned i = 0; i < 21; i++) {
    size_t pos = 3*i;
    if (!(~val & (0b111 << pos))) {
      return true;
    }
  }
  return false;
}

ReducibilityChecker::ReducibilityChecker(DemodulationLHSIndex* index, UnitClauseLiteralIndex* litIndex, const Ordering& ord, const Options& opt)
: _index(index), _litIndex(litIndex), _ord(ord), _opt(opt), _rwTermState(_ord.createState()) {}

bool ReducibilityChecker::pushSidesFromLiteral(Literal* lit, ResultSubstitution* subst, bool result)
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
          if (t0s.isTerm()) {
            _sidesToCheck.push(t0s.term());
            _sidesToCheck2.push(t0);
          }
          if (t1s.isTerm()) {
            _sidesToCheck.push(t1s.term());
            _sidesToCheck2.push(t1);
          }
          break;
        case Ordering::GREATER:
        case Ordering::GREATER_EQ:
          if (t0s.isTerm()) {
            _sidesToCheck.push(t0s.term());
            _sidesToCheck2.push(t0);
          }
          break;
        case Ordering::LESS:
        case Ordering::LESS_EQ:
          if (t1s.isTerm()) {
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
      _sidesToCheck.push(subst->apply(t0,result).term());
      _sidesToCheck2.push(t0);
      break;
    }
    case Ordering::LESS:
    case Ordering::LESS_EQ: {
      ASS(t1.isTerm());
      _sidesToCheck.push(subst->apply(t1,result).term());
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
    // cout << "bound " << var << " " << term << endl;
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
    TermList* inserted;
    if (term.isTerm()) {
      renaming = false;
    }
    return _map.getValuePtr(var, inserted, term) || *inserted == term;
  }

  void specVar(unsigned var, TermList term) const
  {
    ASSERTION_VIOLATION;
  }

  bool renaming = true;
  DHMap<unsigned,TermList> _map;
};

bool ReducibilityChecker::checkSup(Literal* rwLit, Literal* eqLit, TermList eqLHS, Term* rwTerm, Term* rwTermS, TermList tgtTermS, ResultSubstitution* subst, bool eqIsResult, Ordering::Result rwComp, bool eqClauseUnit)
{
  TIME_TRACE("ReducibilityChecker::checkSup");
  if (_opt.reducibilityCheck()==Options::ReducibilityCheck::OFF) {
    return false;
  }
  _ord.initStateForTerm(_rwTermState, rwTermS);
  vstringstream exp;
  if (pushSidesFromLiteral(rwLit, subst, !eqIsResult)) {
    return true;
  }
  if (rwLit->isEquality()) {
    OneEqBinder binder;
    if (_sidesToCheck.size()==2 && _sidesToCheck[0]->functor()==_sidesToCheck[1]->functor() && MatchingUtils::matchArgs(_sidesToCheck[0],_sidesToCheck[1],binder)) {
      setBits(binder.b, binder.v, PoComp::EQ, _reducedUnder);
    }
  }
  auto r = checkLiteral(rwTermS, &tgtTermS, exp, rwTerm);
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
    if (!_ord.isGreater(tgtTermS,rhs,nullptr,&_constraintsFromComparison)) {
      LOG1(exp,"not greater tgtTerm");
      for (const auto& c : _constraintsFromComparison) {
        auto l = get<0>(c);
        auto r = get<1>(c);
        auto strict = get<2>(c);
        setBits(l, r, PoComp::GT, _reducedUnder);
        if (!strict) {
          setBits(l, r, PoComp::EQ, _reducedUnder);
        }
        if (isReducedUnderAny(_reducedUnder)) {
          return true;
        }
      }
      continue;
    }
    return true;
  }

  DHMap<pair<TermList,Term*>,uint64_t>::Iterator rcIt(ptr->reducesToCond);
  while (rcIt.hasNext()) {
    pair<TermList,Term*> kv;
    uint64_t val;
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
    if (!_ord.isGreater(tgtTermS,rhs,nullptr,&_constraintsFromComparison)) {
      for (const auto& c : _constraintsFromComparison) {
        auto l = get<0>(c);
        auto r = get<1>(c);
        auto strict = get<2>(c);
        bool reversed = l > r;
        auto idx_x = std::min(l,r);
        auto idx_y = std::max(l,r);
        size_t idx = idx_y*(idx_y-1)/2 + idx_x;
        size_t pos_gt = 3*idx;
        size_t pos_eq = 3*idx+1;
        size_t pos_lt = 3*idx+2;

        if (val & (1UL << (reversed ? pos_lt : pos_gt))) {
          _reducedUnder |= 1UL << (reversed ? pos_lt : pos_gt);
        }
        if (!strict && (val & (1UL << (reversed ? pos_lt : pos_gt)))) {
          _reducedUnder |= 1UL << pos_eq;
        }
        if (isReducedUnderAny(_reducedUnder)) {
          return true;
        }
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
      vstringstream exp;
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
      auto res = checkLiteral(nullptr, nullptr, exp, nullptr);
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

bool ReducibilityChecker::checkLiteralSanity(Literal* lit, Term* rwTermS, vstringstream& exp)
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
        bool preordered = false;
        if (!getDemodulationRHSCodeTree(qr, st, rhsS, &preordered)) {
          continue;
        }
        if (!preordered && !_ord.isGreater(TermList(st),rhsS)) {
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

bool ReducibilityChecker::checkRwTermSanity(Term* rwTermS, TermList tgtTermS, vstringstream& exp)
{
  LOG2(exp,"check rwTerm ",*rwTermS);
  auto it = _index->getGeneralizations(rwTermS,true);
  while (it.hasNext()) {
    auto qr = it.next();
    TermList rhsS;
    if (!getDemodulationRHSCodeTree(qr, rwTermS, rhsS, nullptr)) {
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

bool ReducibilityChecker::getDemodulationRHSCodeTree(const TermQueryResult& qr, Term* lhsS, TermList& rhsS, bool* preordered)
{
  TIME_TRACE("ReducibilityChecker::getDemodulationRHSCodeTree");
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
  Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
  if (preordered && (argOrder==Ordering::LESS || argOrder==Ordering::GREATER)) {
    *preordered = true;
    return true;
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
      if (!_ord.isGreater(TermList(t),rhsS,nullptr,&_constraintsFromComparison)) {
        LOG1(cout,"not greater");
        for (const auto& c : _constraintsFromComparison) {
          auto l = get<0>(c);
          auto r = get<1>(c);
          auto strict = get<2>(c);
          bool reversed = l > r;
          auto idx_x = std::min(l,r);
          auto idx_y = std::max(l,r);
          size_t idx = idx_y*(idx_y-1)/2 + idx_x;
          size_t pos_gt = 3*idx;
          size_t pos_eq = 3*idx+1;
          size_t pos_lt = 3*idx+2;

          t->reducesUnder() |= 1UL << (reversed ? pos_lt : pos_gt);
          if (!strict) {
            t->reducesUnder() |= 1UL << pos_eq;
          }
          uint64_t* ptr;
          e->reducesToCond.getValuePtr(make_pair(rhsS,lhs.term()), ptr, 0);
          (*ptr) |= 1UL << (reversed ? pos_lt : pos_gt);
          if (!strict) {
            (*ptr) |= 1UL << pos_eq;
          }
          changed.insert(t);
        }
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
    if (!getDemodulationRHSCodeTree(qr, t, rhsS, nullptr)) {
      continue;
    }
    LOG2(cout,"rhs ",rhsS);
    if (!_ord.isGreater(TermList(t),rhsS,nullptr,&_constraintsFromComparison)) {
      for (const auto& c : _constraintsFromComparison) {
        auto l = get<0>(c);
        auto r = get<1>(c);
        auto strict = get<2>(c);
        bool reversed = l > r;
        auto idx_x = std::min(l,r);
        auto idx_y = std::max(l,r);
        size_t idx = idx_y*(idx_y-1)/2 + idx_x;
        size_t pos_gt = 3*idx;
        size_t pos_eq = 3*idx+1;
        size_t pos_lt = 3*idx+2;

        t->reducesUnder() |= 1UL << (reversed ? pos_lt : pos_gt);
        if (!strict) {
          t->reducesUnder() |= 1UL << pos_eq;
        }
        uint64_t* ptr;
        e->reducesToCond.getValuePtr(make_pair(rhsS,qr.term.term()), ptr, 0);
        (*ptr) |= 1UL << (reversed ? pos_lt : pos_gt);
        if (!strict) {
          (*ptr) |= 1UL << pos_eq;
        }
      }
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

bool ReducibilityChecker::checkLiteral(Term* rwTermS, TermList* tgtTermS, vstringstream& exp, Term* rwTerm)
{
  ASS(_sidesToCheck.isNonEmpty());
  DHSet<Term*> checked;
  // TODO where should we handle rwTerm?
  checked.insert(rwTermS);

  for (Term* side : _sidesToCheck) {
    if (_sidesToCheck.size()>1 && !side->containsSubterm(TermList(rwTermS))) {
      continue;
    }
    NonVariableNonTypeIterator stit(side, !side->isLiteral());
    while (stit.hasNext()) {
      auto st = stit.next();
      LOG2(exp,"checking subterm ",st->toString());
      if (!_attempted.insert(st)) {
        LOG1(exp,"already checked");
        stit.right();
        continue;
      }
      if (rwTermS && !_ord.isGreater(TermList(rwTermS),TermList(st),_rwTermState,&_constraintsFromComparison)) {
        for (const auto& c : _constraintsFromComparison) {
          auto l = get<0>(c);
          auto r = get<1>(c);
          auto strict = get<2>(c);
          bool reversed = l > r;
          auto idx_x = std::min(l,r);
          auto idx_y = std::max(l,r);
          size_t idx = idx_y*(idx_y-1)/2 + idx_x;
          size_t pos_gt = 3*idx;
          size_t pos_eq = 3*idx+1;
          size_t pos_lt = 3*idx+2;

          if (st->isReduced() || (st->reducesUnder() & 1UL << (reversed ? pos_lt : pos_gt))) {
            _reducedUnder |= 1UL << (reversed ? pos_lt : pos_gt);
          }
          if (!strict && (st->isReduced() || (st->reducesUnder() & 1UL << pos_eq))) {
            _reducedUnder |= 1UL << pos_eq;
          }
          if (isReducedUnderAny(_reducedUnder)) {
            TIME_TRACE("conditionally reduced");
            return true;
          }
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
        TIME_TRACE("conditionally reduced");
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
  void* stSstate = _ord.createState();
  ASS(_sidesToCheck.size()==_sidesToCheck2.size());
  for (unsigned i = 0; i < _sidesToCheck.size(); i++) {
    auto sideS = _sidesToCheck[i];
    auto side = _sidesToCheck2[i];

    if (side.isVar()) {
      continue;
    }
    if (_sidesToCheck.size()>1 && !sideS->containsSubterm(TermList(rwTermS))) {
      continue;
    }

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
        TIME_TRACE("st ground");
        stit.right();
        continue;
      }
      // auto e = getCacheEntryForTerm(stS.term());
      // auto ce = static_cast<ReducibilityChecker::ReducibilityEntry*>(stS.term()->reducibilityInfo());
      // if (ce && !argReduced(stS.term())) {
      //   TIME_TRACE("info cached");
      //   DHSet<pair<TermList,Term*>>::Iterator rIt(ce->reducesTo);
      //   while (rIt.hasNext()) {
      //     auto kv = rIt.next();
      //     // DHSet<unsigned> vars;
      //     // bool ok = true;
      //     // for (unsigned j = 0; j < kv.second->arity(); j++) {
      //     //   if (kv.second->nthArgument(j)->isTerm() || !vars.insert(kv.second->nthArgument(j)->var())) {
      //     //     ok = false;
      //     //     break;
      //     //   }
      //     // }
      //     // if (ok) {
      //     //   TIME_TRACE("most general");
      //     // }
      //     RobSubstitution rsubst;
      //     {TIME_TRACE("unify");
      //     ALWAYS(rsubst.unify(TermList(kv.second),0,st,1));}

      //     auto rwTermO = rsubst.apply(TermList(rwTerm),1);
      //     Binder b;
      //     if (MatchingUtils::matchTerms(rwTermO, TermList(rwTermS), b) && !b.renaming) {
      //       TIME_TRACE("this check cached");
      //       return true;
      //     }
      //   }
      // } else {
        _ord.initStateForTerm(stSstate,stS.term());
        auto git = _index->getGeneralizations(stS.term(), true, e);
        while (git.hasNext()) {
          auto qr = git.next();
          if (!qr.clause->noSplits()) {
            continue;
          }
          static RobSubstitution subst;
          TypedTermList trm(stS.term());
          bool resultTermIsVar = qr.term.isVar();
          if (resultTermIsVar) {
            TermList querySort = trm.sort();
            TermList eqSort = SortHelper::getEqualityArgumentSort(qr.literal);
            subst.reset();
            if (!subst.match(eqSort, 0, querySort, 1)) {
              continue;
            }
          }
          TermList rhs = EqHelper::getOtherEqualitySide(qr.literal,qr.term);
          Ordering::Result argOrder = _ord.getEqualityArgumentOrder(qr.literal);
          bool oriented = true;
          uint64_t bits = 0;
          // TODO !!!!!!!!! enable constraints below
          // if (!(argOrder==Ordering::LESS || argOrder==Ordering::GREATER) && !_ord.isGreater(TermList(stS),rhsS,stSstate,&_constraintsFromComparison)) {
          if (argOrder!=Ordering::LESS && argOrder!=Ordering::GREATER && !_ord.isGreater(TermList(stS),rhs,stSstate,&_constraintsFromComparison,qr.substitution.ptr())) {
            for (const auto& c : _constraintsFromComparison) {
              auto l = get<0>(c);
              auto r = get<1>(c);
              auto strict = get<2>(c);
              bool reversed = l > r;
              auto idx_x = std::min(l,r);
              auto idx_y = std::max(l,r);
              size_t idx = idx_y*(idx_y-1)/2 + idx_x;
              size_t pos_gt = 3*idx;
              size_t pos_eq = 3*idx+1;
              size_t pos_lt = 3*idx+2;

              bits |= 1UL << (reversed ? pos_lt : pos_gt);
              if (!strict) {
                bits |= 1UL << pos_eq;
              }
            }
            oriented = false;
          }
          if (!oriented && !bits) {
            continue;
          }
          static RobSubstitution rsubst;
          rsubst.reset();
          ALWAYS(rsubst.unify(qr.term,0,st,1));

          auto rwTermO = rsubst.apply(TermList(rwTerm),1);
          Binder b;
          if (MatchingUtils::matchTerms(rwTermO, TermList(rwTermS), b) && !b.renaming) {
            if (oriented) {
              return true;
            }
            _reducedUnder |= bits;
            if (isReducedUnderAny(_reducedUnder)) {
              return true;
            }
          }
        }
      // }
    }
    ft->destroy();
  }
  _ord.destroyState(stSstate);

  return false;
}

}