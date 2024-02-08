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
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "NumTraits.hpp"
#include "VarOrder.hpp"

#include "Indexing/Index.hpp"
#include "Inferences/ForwardGroundJoinability.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Set.hpp"

#include "Indexing/Index.hpp"

#include "Shell/Options.hpp"
#include "SubstHelper.hpp"
#include <fstream>

#include "EqHelper.hpp"
#include "Term.hpp"
#include "KBO.hpp"
#include "Signature.hpp"
#include "TermIterators.hpp"
#include "VarOrder.hpp"

#define COLORED_WEIGHT_BOOST 0x10000

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;


/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO::State
{
public:
  /** Initialise the state */
  State(KBO* kbo)
    : _kbo(*kbo)
  {}

  void init()
  {
    _weightDiff=0;
    _posNum=0;
    _negNum=0;
    _lexResult=EQUAL;
    _varDiffs.reset();
  }

  void traverse(Term* t1, Term* t2);
  void traverse(TermList tl,int coefficient);
  Result result(Term* t1, Term* t2);

private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(TermList t1, TermList t2);
  Result applyVariableCondition(Result res)
  {
    if(_posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    } else if(_negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    }
    return res;
  }

  int _weightDiff;
  DHMap<unsigned, int, IdentityHash, DefaultHash> _varDiffs;
  /** Number of variables, that occur more times in the first literal */
  int _posNum;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** First comparison result */
  Result _lexResult;
  /** The ordering used */
  KBO& _kbo;
  /** The variable counters */
}; // class KBO::State

struct LeftState {
  Term* t;
  DHMap<unsigned, int, IdentityHash, DefaultHash> varCnts;
  bool ready = false;
};

class KBO::StateGreater
{
public:
  /** Initialise the state */
  StateGreater(KBO* kbo) : _kbo(*kbo) {}

  void init(LeftState* ls)
  {
    _negNum=0;
    _varDiffs.reset();
    _varDiffs.loadFromMap(ls->varCnts);
    _ls = ls;
  }

  void initState(LeftState* ls)
  {
    ls->varCnts.reset();
    ls->varCnts.loadFromMap(_varDiffs);
    ls->ready = true;
  }

  void init()
  {
    _negNum=0;
    _varDiffs.reset();
    _ls = nullptr;
  }

  void setConstraints(VarOrderBV* constraints, VarOrderBV* newConstraints)
  {
    _constraints = constraints;
    _newConstraints = newConstraints;
  }

  USE_ALLOCATOR(StateGreater);

  bool traverse(Term* t1, Term* t2);
  void traverseVars(TermList tl, int coef);
  Result result(Term* t1, Term* t2);
  bool checkVars() const;
private:
  void recordVariable(unsigned var, int coef);

  /** The variable counters */
  DHMap<unsigned, int, IdentityHash, DefaultHash> _varDiffs;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** The ordering used */
  KBO& _kbo;
  LeftState* _ls;
  VarOrderBV* _constraints;
  VarOrderBV* _newConstraints;
}; // class KBO::State

class KBO::StateGreaterSubst
{
public:
  /** Initialise the state */
  StateGreaterSubst(KBO* kbo) : _kbo(*kbo) {}

  void init(LeftState* ls, Indexing::ResultSubstitution* subst)
  {
    _subst=subst;
    _negNum=0;
    _varDiffs.reset();
    _varDiffs.loadFromMap(ls->varCnts);
    _ls = ls;
  }

  void initState(LeftState* ls)
  {
    ls->varCnts.reset();
    ls->varCnts.loadFromMap(_varDiffs);
    ls->ready = true;
  }

  void init(Indexing::ResultSubstitution* subst)
  {
    _subst=subst;
    _negNum=0;
    _varDiffs.reset();
    _ls = nullptr;
  }

  void setConstraints(VarOrderBV* constraints, VarOrderBV* newConstraints)
  {
    _constraints = constraints;
    _newConstraints = newConstraints;
  }

  USE_ALLOCATOR(StateGreaterSubst);

  bool traverse(Term* t1, Term* t2, bool weightsOk);
  void traverseVars2(TermList tl);
  void traverseVars(TermList tl, int coef);
  Result result(Term* t1, Term* t2);
  bool checkVars() const;
private:
  void recordVariable(unsigned var, int coef);

  /** The variable counters */
  DHMap<unsigned, int, IdentityHash, DefaultHash> _varDiffs;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** The ordering used */
  KBO& _kbo;
  LeftState* _ls;
  VarOrderBV* _constraints;
  VarOrderBV* _newConstraints;
  Indexing::ResultSubstitution* _subst;
}; // class KBO::StateGreaterSubst

class KBO::StateGreaterVO
{
public:
  /** Initialise the state */
  StateGreaterVO(KBO* kbo) : _kbo(*kbo) {}

  void init()
  {
    _negNum=0;
    _varsLeft.reset();
    _varsRight.reset();
    _varDiffs.reset();
  }

  USE_ALLOCATOR(StateGreaterVO);

  bool traverse(Term* t1, Term* t2, VarOrder& vo);
  Result result(Term* t1, Term* t2);
  bool checkVars(VarOrder& vo) const;
  void traverseVars(TermList tl, bool left, VarOrder& vo);
private:
  void recordVariable(unsigned var, bool left, VarOrder& vo);

  /** The variable counters */
  DHMap<unsigned, unsigned, IdentityHash, DefaultHash> _varsLeft;
  DHMap<unsigned, unsigned, IdentityHash, DefaultHash> _varsRight;
  DHMap<unsigned, int, IdentityHash, DefaultHash> _varDiffs;
  /** Number of variables, that occur more times in the second literal */
  int _negNum;
  /** The ordering used */
  KBO& _kbo;
}; // class KBO::State

/**
 * Return result of comparison between @b l1 and @b l2 under
 * an assumption, that @b traverse method have been called
 * for both literals. (Either traverse(Term*,Term*) or
 * traverse(Term*,int) for both terms/literals in case their
 * top functors are different.)
 */
Ordering::Result KBO::State::result(Term* t1, Term* t2)
{
  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else if(t1->functor()!=t2->functor()) {
    if(t1->isLiteral()) {
      int prec1, prec2;
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    } else if(t1->isSort()){
      ASS(t2->isSort()); //should only compare sorts with sorts
      res=_kbo.compareTypeConPrecedences(t1->functor(), t2->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    } else {
      res=_kbo.compareFunctionPrecedences(t1->functor(), t2->functor());
      ASS_REP(res==GREATER || res==LESS, res); //precedence ordering must be total
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);

  //the result should never be EQUAL:
  //- either t1 and t2 are truely equal. But then if they're equal, it
  //would have been discovered by the t1==t2 check in
  //KBO::compare methods.
  //- or literals t1 and t2 are equal but for their polarity. But such
  //literals should never occur in a clause that would exist long enough
  //to get to ordering --- it should be deleted by tautology deletion.
  ASS_NEQ(res, EQUAL);
  return res;
}

Ordering::Result KBO::State::innerResult(TermList tl1, TermList tl2)
{
  ASS_NEQ(tl1, tl2);
  ASS(!TermList::sameTopFunctor(tl1,tl2));

  if(_posNum>0 && _negNum>0) {
    return INCOMPARABLE;
  }

  Result res;
  if(_weightDiff) {
    res=_weightDiff>0 ? GREATER : LESS;
  } else {
    if(tl1.isVar()) {
      ASS_EQ(_negNum,0);
      res=LESS;
    } else if(tl2.isVar()) {
      ASS_EQ(_posNum,0);
      res=GREATER;
    } else if(tl1.term()->isSort()){
      res=_kbo.compareTypeConPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    } else {
      res=_kbo.compareFunctionPrecedences(tl1.term()->functor(), tl2.term()->functor());
      ASS_REP(res==GREATER || res==LESS, res);//precedence ordering must be total
    }
  }
  return applyVariableCondition(res);
}

void KBO::State::recordVariable(unsigned var, int coef)
{
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    } else if(*pnum==1) {
      _posNum++;
    }
  } else {
    if(*pnum==0) {
      _posNum--;
    } else if(*pnum==-1) {
      _negNum++;
    }
  }
}

void KBO::State::traverse(TermList tl,int coef)
{
  if(tl.isOrdinaryVar()) {
    _weightDiff += _kbo._funcWeights._specialWeights._variableWeight * coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  _weightDiff+=_kbo.symbolWeight(t)*coef;

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      auto term = ts->term();
      _weightDiff+=_kbo.symbolWeight(term)*coef;
      if(term->arity()) {
	stack.push(term->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      auto var = ts->var();
      _weightDiff += _kbo._funcWeights._specialWeights._variableWeight * coef;
      recordVariable(var, coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void KBO::State::traverse(Term* t1, Term* t2)
{
  ASS(t1->functor()==t2->functor());
  ASS(t1->arity());
  ASS_EQ(_lexResult, EQUAL);

  unsigned depth=1;
  unsigned lexValidDepth=0;

  static Stack<TermList*> stack(32);
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(!stack.isEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      depth--;
      ASS_NEQ(_lexResult,EQUAL);
      if(_lexResult!=EQUAL && depth<lexValidDepth) {
	lexValidDepth=depth;
	if(_weightDiff!=0) {
	  _lexResult=_weightDiff>0 ? GREATER : LESS;
	}
	_lexResult=applyVariableCondition(_lexResult);
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neighter weightDiff nor varDiffs would change
      continue;
    }
    if(TermList::sameTopFunctor(*ss,*tt)) {
      ASS(ss->isTerm());
      ASS(tt->isTerm());
      ASS(ss->term()->arity());
      stack.push(ss->term()->args());
      stack.push(tt->term()->args());
      depth++;
    } else {
      traverse(*ss,1);
      traverse(*tt,-1);
      if(_lexResult==EQUAL) {
	_lexResult=innerResult(*ss, *tt);
	lexValidDepth=depth;
	ASS(_lexResult!=EQUAL);
	ASS(_lexResult!=GREATER_EQ);
	ASS(_lexResult!=LESS_EQ);
      }
    }
  }
  ASS_EQ(depth,0);
}

// StateGreater

void KBO::StateGreater::recordVariable(unsigned var, int coef)
{
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    }
  } else {
    if(*pnum==-1) {
      _negNum++;
    }
  }
}

void KBO::StateGreater::traverseVars(TermList tl, int coef)
{
  if(tl.isOrdinaryVar()) {
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      auto term = ts->term();
      if(term->arity() && !term->ground()) {
        stack.push(term->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

bool KBO::StateGreater::traverse(Term* t1, Term* t2)
{
  ASS_EQ(t1->functor(),t2->functor());
  ASS_EQ(t1->kboWeight(),t2->kboWeight());
  ASS(t1->arity());
  bool stillEqual = true;
  bool greater = true; // true if the unconstrained comparison is still greater

  static Stack<TermList*> stack(32);
  stack.reset();
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(stack.isNonEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      ASS(!stillEqual); // we should have detected the difference earlier
      if (!checkVars()) {
        greater = false;
        if (!_newConstraints || !*_newConstraints) {
          return false;
        }
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neither weightDiff nor varDiffs would change
      continue;
    }
    if (stillEqual) {
      if (_kbo.weight(*ss)<_kbo.weight(*tt)) {
        return false;
      }
      if (_kbo.weight(*ss)>_kbo.weight(*tt)) {
        traverseVars(*ss,1);
        traverseVars(*tt,-1);
        if (!checkVars()) {
          if (!_newConstraints || !*_newConstraints) {
            return false;
          }
          greater = false;
        }
        stillEqual = false;
        continue;
      }
      // weight(*ss)==weight(*tt)
      if (ss->isOrdinaryVar()) {
        if (!tt->isOrdinaryVar() || !_newConstraints) {
          return false;
        }

        ASS(!*_newConstraints);
        if (isBitSet(ss->var(),tt->var(),PoComp::GT,*_constraints)) {
          setBit(ss->var(),tt->var(),PoComp::GT,*_newConstraints);
        } else {
          return false;
        }
        recordVariable(ss->var(),1);
        recordVariable(tt->var(),-1);
        stillEqual = false;
        greater = false;
        continue;
      }
      if (tt->isOrdinaryVar()) {
        traverseVars(*ss,1);
        traverseVars(*tt,-1);
        if (!checkVars()) {
          if (!_newConstraints || !*_newConstraints) {
            return false;
          }
          greater = false;
        }
        stillEqual = false;
        continue;
      }
      Result comp = ss->term()->isSort()
        ? _kbo.compareTypeConPrecedences(ss->term()->functor(),tt->term()->functor())
        : _kbo.compareFunctionPrecedences(ss->term()->functor(),tt->term()->functor());
      switch (comp)
      {
        case Ordering::LESS:
        case Ordering::LESS_EQ: {
          return false;
        }
        case Ordering::GREATER:
        case Ordering::GREATER_EQ: {
          traverseVars(*ss,1);
          traverseVars(*tt,-1);
          if (!checkVars()) {
            if (!_newConstraints || !*_newConstraints) {
              return false;
            }
            greater = false;
          }
          stillEqual = false;
          break;
        }
        case Ordering::EQUAL: {
          stack.push(ss->term()->args());
          stack.push(tt->term()->args());
          break;
        }
        default: ASSERTION_VIOLATION;
      }
    } else {
      traverseVars(*ss,1);
      traverseVars(*tt,-1);
    }
  }
  return greater && !stillEqual && checkVars();
}

bool KBO::StateGreater::checkVars() const
{
  if (_newConstraints && (_negNum == 1 || *_newConstraints)) {
    if (_negNum>1) {
      *_newConstraints = 0;
      return _negNum <= 0;
    }
    decltype(_varDiffs)::Iterator it(_varDiffs);
    while (it.hasNext()) {
      unsigned var;
      int cnt;
      it.next(var,cnt);
      if (cnt>=0) {
        continue;
      }
      if (!*_newConstraints) {
        decltype(_varDiffs)::Iterator it2(_varDiffs);
        while (it2.hasNext()) {
          unsigned var2;
          int cnt2;
          it2.next(var2,cnt2);
          if (var!=var2 && cnt2>=(-cnt)) {
            if (isBitSet(var2,var,PoComp::EQ,*_constraints)) {
              setBit(var2,var,PoComp::EQ,*_newConstraints);
            }
            if (isBitSet(var2,var,PoComp::GT,*_constraints)) {
              setBit(var2,var,PoComp::GT,*_newConstraints);
            }
          }
        }
      } else {
        VarOrderBV mask = 0;
        for (unsigned i = 0; i <= 6; i++) {
          if (i==var) {
            continue;
          }
          auto ptr = _varDiffs.findPtr(i);
          if (!ptr || *ptr<(-cnt)) {
            continue;
          }
          setBit(i,var,PoComp::EQ,mask);
          setBit(i,var,PoComp::GT,mask);
        }
        *_newConstraints &= mask;
      }
      if (!*_newConstraints) {
        break;
      }
    }
  }
  return _negNum <= 0;
}

// StateGreaterSubst

void KBO::StateGreaterSubst::recordVariable(unsigned var, int coef)
{
  ASS(coef==1 || coef==-1);

  int* pnum;
  _varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      _negNum--;
    }
  } else {
    if(*pnum==-1) {
      _negNum++;
    }
  }
}

void KBO::StateGreaterSubst::traverseVars(TermList tl, int coef)
{
  if(tl.isOrdinaryVar()) {
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      auto term = ts->term();
      if(term->arity() && !term->ground()) {
        stack.push(term->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void KBO::StateGreaterSubst::traverseVars2(TermList tl)
{
  if(tl.isOrdinaryVar()) {
    traverseVars(_subst->applyToBoundResult(tl.var()),-1);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      auto term = ts->term();
      if(term->arity() && !term->ground()) {
        stack.push(term->args());
      }
    } else {
      ASS(ts->isOrdinaryVar());
      traverseVars(_subst->applyToBoundResult(ts->var()),-1);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

bool KBO::StateGreaterSubst::traverse(Term* t1, Term* t2, bool weightsOk)
{
  ASS_EQ(t1->functor(),t2->functor());
  ASS(weightsOk || t1->kboWeight()==t2->kboWeight2());
  // ASS(t1->arity()); // we cannot check for equality outside, so this is commented
  bool stillEqual = true;
  bool greater = true; // true if the unconstrained comparison is still greater

  static Stack<TermList*> lstack(16);
  static Stack<pair<TermList*,bool>> rstack(16);
  lstack.reset();
  rstack.reset();
  lstack.push(t1->args());
  rstack.push(make_pair(t2->args(),false));
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(lstack.isNonEmpty()) {
    ASS(rstack.isNonEmpty());
    ss = lstack.pop();
    auto kv = rstack.pop();
    bool underSubst = kv.second;
    tt = kv.first;
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      if (stillEqual) {
        continue;
      }
      // ASS(!stillEqual); // we should have detected the difference earlier
      if (!checkVars()) {
        greater = false;
        if (!_newConstraints || !*_newConstraints) {
          return false;
        }
      }
      continue;
    }

    lstack.push(ss->next());
    rstack.push(make_pair(tt->next(),underSubst));
    auto t = (tt->isVar() && !underSubst) ? _subst->applyToBoundResult(tt->var()) : *tt;
    if (tt->isVar()) {
      underSubst = true;
    }
    if (underSubst && ss->sameContent(&t)) {
      //if content is the same, neither weightDiff nor varDiffs would change
      continue;
    }
    if (stillEqual) {
      if (weightsOk) {
        if (ss->isTerm()) {
          _kbo.computeWeight(ss->term());
        }
        if (t.isTerm()) {
          if (underSubst) {
            _kbo.computeWeight(t.term());
          } else {
            _kbo.computeWeight2(t.term(),_subst);
          }
        }
      }
      if (_kbo.weight(*ss)<_kbo.weight2(t,_subst,underSubst)) {
        return false;
      }
      if (_kbo.weight(*ss)>_kbo.weight2(t,_subst,underSubst)) {
        traverseVars(*ss,1);
        if (underSubst) {
          traverseVars(t,-1);
        } else {
          traverseVars2(t);
        }
        if (!checkVars()) {
          if (!_newConstraints || !*_newConstraints) {
            return false;
          }
          greater = false;
        }
        stillEqual = false;
        continue;
      }
      // weight(*ss)==weight(*tt)
      if (ss->isOrdinaryVar()) {
        if (!t.isOrdinaryVar() || !_newConstraints) {
          return false;
        }

        ASS(underSubst);
        ASS(!*_newConstraints);
        if (isBitSet(ss->var(),t.var(),PoComp::GT,*_constraints)) {
          setBit(ss->var(),t.var(),PoComp::GT,*_newConstraints);
        } else {
          return false;
        }
        recordVariable(ss->var(),1);
        recordVariable(t.var(),-1);
        stillEqual = false;
        greater = false;
        continue;
      }
      if (t.isOrdinaryVar()) {
        ASS(underSubst);
        traverseVars(*ss,1);
        if (underSubst) {
          traverseVars(t,-1);
        } else {
          traverseVars2(t);
        }
        if (!checkVars()) {
          if (!_newConstraints || !*_newConstraints) {
            return false;
          }
          greater = false;
        }
        stillEqual = false;
        continue;
      }
      Result comp = ss->term()->isSort()
        ? _kbo.compareTypeConPrecedences(ss->term()->functor(),t.term()->functor())
        : _kbo.compareFunctionPrecedences(ss->term()->functor(),t.term()->functor());
      switch (comp)
      {
        case Ordering::LESS:
        case Ordering::LESS_EQ: {
          return false;
        }
        case Ordering::GREATER:
        case Ordering::GREATER_EQ: {
          traverseVars(*ss,1);
          if (underSubst) {
            traverseVars(t,-1);
          } else {
            traverseVars2(t);
          }
          if (!checkVars()) {
            if (!_newConstraints || !*_newConstraints) {
              return false;
            }
            greater = false;
          }
          stillEqual = false;
          break;
        }
        case Ordering::EQUAL: {
          lstack.push(ss->term()->args());
          rstack.push(make_pair(t.term()->args(),underSubst));
          break;
        }
        default: ASSERTION_VIOLATION;
      }
    } else {
      traverseVars(*ss,1);
      if (underSubst) {
        traverseVars(t,-1);
      } else {
        traverseVars2(t);
      }
    }
  }
  return greater && !stillEqual && checkVars();
}

bool KBO::StateGreaterSubst::checkVars() const
{
  if (_newConstraints && (_negNum == 1 || *_newConstraints)) {
    if (_negNum>1) {
      *_newConstraints = 0;
      return _negNum <= 0;
    }
    decltype(_varDiffs)::Iterator it(_varDiffs);
    while (it.hasNext()) {
      unsigned var;
      int cnt;
      it.next(var,cnt);
      if (cnt>=0) {
        continue;
      }
      if (!*_newConstraints) {
        decltype(_varDiffs)::Iterator it2(_varDiffs);
        while (it2.hasNext()) {
          unsigned var2;
          int cnt2;
          it2.next(var2,cnt2);
          if (var!=var2 && cnt2>=(-cnt)) {
            if (isBitSet(var2,var,PoComp::EQ,*_constraints)) {
              setBit(var2,var,PoComp::EQ,*_newConstraints);
            }
            if (isBitSet(var2,var,PoComp::GT,*_constraints)) {
              setBit(var2,var,PoComp::GT,*_newConstraints);
            }
          }
        }
      } else {
        VarOrderBV mask = 0;
        for (unsigned i = 0; i <= 6; i++) {
          if (i==var) {
            continue;
          }
          auto ptr = _varDiffs.findPtr(i);
          if (!ptr || *ptr<(-cnt)) {
            continue;
          }
          setBit(i,var,PoComp::EQ,mask);
          setBit(i,var,PoComp::GT,mask);
        }
        *_newConstraints &= mask;
      }
      if (!*_newConstraints) {
        break;
      }
    }
  }
  return _negNum <= 0;
}

// StateGreaterVO

void KBO::StateGreaterVO::recordVariable(unsigned var, bool left, VarOrder& vo)
{
  unsigned* pnum;
  if (left) {
    _varsLeft.getValuePtr(var,pnum);
  } else {
    _varsRight.getValuePtr(var,pnum);
  }
  (*pnum)++;
  int* pdiff;
  _varDiffs.getValuePtr(var,pdiff,0);
  (*pdiff)+=left?1:-1;
}

void KBO::StateGreaterVO::traverseVars(TermList tl, bool left, VarOrder& vo)
{
  TIME_TRACE("KBO::StateGreaterVO::traverseVars");
  if(tl.isOrdinaryVar()) {
    recordVariable(tl.var(), left, vo);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  if(!t->arity()) {
    return;
  }

  TermList* ts=t->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      auto term = ts->term();
      if(term->arity() && !term->ground()) {
        stack.push(term->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      recordVariable(ts->var(), left, vo);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

bool KBO::StateGreaterVO::traverse(Term* t1, Term* t2, VarOrder& vo)
{
  TIME_TRACE("KBO::StateGreaterVO::traverse");
  ASS_EQ(t1->functor(),t2->functor());
  ASS_EQ(t1->kboWeight(),t2->kboWeight());
  ASS(t1->arity());
  bool stillEqual = true;

  static Stack<TermList*> stack(32);
  stack.reset();
  stack.push(t1->args());
  stack.push(t2->args());
  TermList* ss; //t1 subterms
  TermList* tt; //t2 subterms
  while(stack.isNonEmpty()) {
    tt=stack.pop();
    ss=stack.pop();
    if(ss->isEmpty()) {
      ASS(tt->isEmpty());
      ASS(!stillEqual); // we should have detected the difference earlier
      if (!checkVars(vo)) {
        return false;
      }
      continue;
    }

    stack.push(ss->next());
    stack.push(tt->next());
    if(ss->sameContent(tt)) {
      //if content is the same, neither weightDiff nor varDiffs would change
      continue;
    }
    if (stillEqual) {
      if (_kbo.weight(*ss)<_kbo.weight(*tt)) {
        return false;
      }
      if (_kbo.weight(*ss)>_kbo.weight(*tt)) {
        traverseVars(*ss,true,vo);
        traverseVars(*tt,false,vo);
        if (!checkVars(vo)) {
          return false;
        }
        stillEqual = false;
        continue;
      }
      // weight(*ss)==weight(*tt)
      if (ss->isOrdinaryVar()) {
        if (!tt->isOrdinaryVar() || !vo.add_gt(ss->var(),tt->var())) {
          return false;
        }
        traverseVars(*ss,true,vo);
        traverseVars(*tt,false,vo);
        stillEqual = false;
        continue;
      }
      if (tt->isOrdinaryVar()) {
        if (!ss->containsSubterm(*tt)) {
          return false; // TODO
        }
        traverseVars(*ss,true,vo);
        traverseVars(*tt,false,vo);
        stillEqual = false;
        continue;
      }
      Result comp = ss->term()->isSort()
        ? _kbo.compareTypeConPrecedences(ss->term()->functor(),tt->term()->functor())
        : _kbo.compareFunctionPrecedences(ss->term()->functor(),tt->term()->functor());
      switch (comp)
      {
        case Ordering::LESS:
        case Ordering::LESS_EQ: {
          return false;
        }
        case Ordering::GREATER:
        case Ordering::GREATER_EQ: {
          traverseVars(*ss,true,vo);
          traverseVars(*tt,false,vo);
          if (!checkVars(vo)) {
            return false;
          }
          stillEqual = false;
          break;
        }
        case Ordering::EQUAL: {
          stack.push(ss->term()->args());
          stack.push(tt->term()->args());
          break;
        }
        default: ASSERTION_VIOLATION;
      }
    } else {
      traverseVars(*ss,true,vo);
      traverseVars(*tt,false,vo);
    }
  }
  return !stillEqual && checkVars(vo);
}

bool KBO::StateGreaterVO::checkVars(VarOrder& vo) const
{
  TIME_TRACE("check vars");
  // DHSet<unsigned>::Iterator varIt(_vars);
  auto varRIt = _varsRight.domain();
  while (varRIt.hasNext()) {
    auto vr = varRIt.next();
    // cout << "checking " << v << endl;
    // auto leftPtr = _varsLeft.findPtr(v);
    unsigned lcnt = 0;
    auto varLIt = _varsLeft.domain();
    while (varLIt.hasNext()) {
      auto vl = varLIt.next();
      auto c = vo.query(vl,vr);
      if (c == PoComp::GT || c == PoComp::EQ) {
        lcnt += _varsLeft.get(vl);
      } else if (c == PoComp::INC) {
        // TODO save for later
      }
    }
    auto rcnt = _varsRight.get(vr);
    if (lcnt < rcnt) {
      return false;
    }
  }

  return true;
}

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
struct PredSigTraits {
  static const char* symbolKindName() 
  { return "predicate"; }

  static unsigned nSymbols() 
  { return env.signature->predicates(); }

  static bool isColored(unsigned functor) 
  { return env.signature->predicateColored(functor);}

  static bool tryGetFunctor(const vstring& sym, unsigned arity, unsigned& out) 
  { return env.signature->tryGetPredicateNumber(sym,arity, out); }

  static const vstring& weightFileName(const Options& opts) 
  { return opts.predicateWeights(); } 

  static bool isUnaryFunction (unsigned functor) 
  { return false; }

  static bool isConstantSymbol(unsigned functor) 
  { return false; } 

  static Signature::Symbol* getSymbol(unsigned functor) 
  { return env.signature->getPredicate(functor); } 
};
#endif


struct FuncSigTraits {
  static const char* symbolKindName() 
  { return "function"; }

  static unsigned nSymbols() 
  { return env.signature->functions(); } 

  static bool isColored(unsigned functor) 
  { return env.signature->functionColored(functor);}

  static bool tryGetFunctor(const vstring& sym, unsigned arity, unsigned& out) 
  { return env.signature->tryGetFunctionNumber(sym,arity, out); }

  static const vstring& weightFileName(const Options& opts) 
  { return opts.functionWeights(); } 

  static bool isUnaryFunction (unsigned functor) 
  { return env.signature->getFunction(functor)->numTermArguments() == 1; } 

  static bool isConstantSymbol(unsigned functor) 
  { return env.signature->getFunction(functor)->numTermArguments() == 0; } 

  static Signature::Symbol* getSymbol(unsigned functor) 
  { return env.signature->getFunction(functor); }
};


template<class SigTraits> 
KboWeightMap<SigTraits> KBO::weightsFromOpts(const Options& opts, const DArray<int>& rawPrecedence) const
{
  auto& str = SigTraits::weightFileName(opts);

  auto arityExtractor = [](unsigned i) { return SigTraits::getSymbol(i)->arity(); };
  auto precedenceExtractor = [&](unsigned i) { return rawPrecedence[i]; };
  auto frequencyExtractor = [](unsigned i) { return SigTraits::getSymbol(i)->usageCnt(); };

  if (!str.empty()) {
    return weightsFromFile<SigTraits>(opts);
  } else {
    switch (opts.kboWeightGenerationScheme()) {
    case Options::KboWeightGenerationScheme::CONST:
      return KboWeightMap<SigTraits>::dflt();
    case Options::KboWeightGenerationScheme::RANDOM:
      return KboWeightMap<SigTraits>::randomized();
    case Options::KboWeightGenerationScheme::ARITY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto _, auto arity) { return arity+1; });
    case Options::KboWeightGenerationScheme::INV_ARITY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto max, auto arity) { return max-arity+1; });
    case Options::KboWeightGenerationScheme::ARITY_SQUARED:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto _, auto arity) { return arity*arity+1; });
    case Options::KboWeightGenerationScheme::INV_ARITY_SQUARED:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(arityExtractor,
        [](auto max, auto arity) { return max*max-arity*arity+1; });
    case Options::KboWeightGenerationScheme::PRECEDENCE:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(precedenceExtractor,
        [](auto _, auto prec) { return prec + 1; });
    case Options::KboWeightGenerationScheme::INV_PRECEDENCE:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(precedenceExtractor,
        [](auto max, auto prec) { return max-prec+1; });
    case Options::KboWeightGenerationScheme::FREQUENCY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(frequencyExtractor,
        [](auto _, auto freq) { return freq > 0 ? freq : 1; });
    case Options::KboWeightGenerationScheme::INV_FREQUENCY:
      return KboWeightMap<SigTraits>::fromSomeUnsigned(frequencyExtractor,
        [](auto max, auto freq) { return max > 0 ? max - freq + 1 : 1; });

    default:
      NOT_IMPLEMENTED;
    }
  }
}

template<class SigTraits> 
KboWeightMap<SigTraits> KBO::weightsFromFile(const Options& opts) const 
{
  DArray<KboWeight> weights(SigTraits::nSymbols());

  ///////////////////////// parsing helper functions ///////////////////////// 
 
  /** opens the file with name f or throws a UserError on failure  */
  auto openFile = [](const vstring& f) -> ifstream {
    ifstream file(f.c_str());
    if (!file.is_open()) {
      throw UserErrorException("failed to open file ", f);
    }
    return file;
  };

  auto parseDefaultSymbolWeight = [&openFile](const vstring& fname) -> unsigned {
    if (!fname.empty()) {
      auto file = openFile(fname);
      for (vstring ln; getline(file, ln);) {
        unsigned dflt;
        vstring special_name;
        bool err = !(vstringstream(ln) >> special_name >> dflt);
        if (!err && special_name == SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT) {
          return dflt;
        }
      }
    }
    return 1; // the default defaultSymbolWeight ;) 
  };

  /** tries to parse line of the form `<special_name> <weight>` */
  auto tryParseSpecialLine = [](const vstring& ln, unsigned& introducedWeight, KboSpecialWeights<SigTraits>& specialWeights) -> bool {
    vstringstream lnstr(ln);

    vstring name;
    unsigned weight;
    bool ok = !!(lnstr >> name >> weight);
    if (ok) {
      if (specialWeights.tryAssign(name, weight)) { return true; }
      else if (name == SPECIAL_WEIGHT_IDENT_DEFAULT_WEIGHT) { /* handled in parseDefaultSymbolWeight */ }
      else if (name == SPECIAL_WEIGHT_IDENT_INTRODUCED    ) { introducedWeight = weight; } 
      else {
        throw Lib::UserErrorException("no special symbol with name '", name, "' (existing ones: " SPECIAL_WEIGHT_IDENT_VAR ", " SPECIAL_WEIGHT_IDENT_INTRODUCED " )");
      }
    }
    return ok;
  };

  /** tries to parse line of the form `<name> <arity> <weight>` */
  auto tryParseNormalLine = [&](const vstring& ln) -> bool {
    vstringstream lnstr(ln);

    vstring name;
    unsigned arity;
    unsigned weight;
    bool ok = !!(lnstr >> name >> arity >> weight);
    if (ok) {
      unsigned i; 
      if (SigTraits::tryGetFunctor(name, arity, i)) {
        weights[i] = SigTraits::isColored(i) 
          ? weight * COLORED_WEIGHT_BOOST
          : weight;
      } else {
        throw Lib::UserErrorException("no ", SigTraits::symbolKindName(), " '", name, "' with arity ", arity);
      }
    }
    return ok;
  };

  ///////////////////////// actual parsing ///////////////////////// 

  auto& filename = SigTraits::weightFileName(opts);
  auto defaultSymbolWeight = parseDefaultSymbolWeight(filename);

  for (unsigned i = 0; i < SigTraits::nSymbols(); i++) {
    weights[i] = SigTraits::isColored(i) 
          ? defaultSymbolWeight * COLORED_WEIGHT_BOOST 
          : defaultSymbolWeight;
  }

  unsigned introducedWeight = defaultSymbolWeight;
  auto specialWeights = KboSpecialWeights<SigTraits>::dflt();

  ASS(!filename.empty());

  auto file = openFile(filename);

  for (vstring ln; getline(file, ln);) {
    if (!tryParseNormalLine(ln) && !tryParseSpecialLine(ln, introducedWeight, specialWeights)) {
      throw Lib::UserErrorException(
             "failed to read line from file ",   filename, "\n",
             "expected syntax: '<name> <arity> <weight>'", "\n",
             "e.g.:            '$add   2       4       '", "\n",
             "or syntax: '<special_name> <weight>'"      , "\n",
             "e.g.:      '$var           7       '"      , "\n"
      );
    } 
  }

  return KboWeightMap<SigTraits> {
    ._weights                = weights,
    ._introducedSymbolWeight = introducedWeight,
    ._specialWeights         = specialWeights,
  };

}

void throwError(UserErrorException e) { throw e; }
void warnError(UserErrorException e) { 
  env.beginOutput();
  env.out() << "WARNING: Your KBO is probably not well-founded. Reason: " << e.msg() << std::endl;
  env.endOutput();
}


KBO::KBO(
    // KBO params
    KboWeightMap<FuncSigTraits> funcWeights, 
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
    KboWeightMap<PredSigTraits> predWeights, 
#endif

    // precedence ordering params
    DArray<int> funcPrec,
    DArray<int> typeConPrec,     
    DArray<int> predPrec, 
    DArray<int> predLevels, 

    // other
    bool reverseLCM
  ) : PrecedenceOrdering(funcPrec, typeConPrec, predPrec, predLevels, reverseLCM)
  , _funcWeights(funcWeights)
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  , _predWeights(predWeights)
#endif
  , _state(new State(this))
  , _stateGt(new StateGreater(this))
  , _stateGtVo(new StateGreaterVO(this))
  , _stateGtSubst(new StateGreaterSubst(this))
{ 
  checkAdmissibility(throwError);
}

KBO KBO::testKBO() 
{

  auto predLevels = []() -> DArray<int>{
    DArray<int> out(env.signature->predicates());
    out.init(out.size(), 1);
    return out;
  };

  return KBO(
      KboWeightMap<FuncSigTraits>::randomized(),
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
      KboWeightMap<PredSigTraits>::randomized(), 
#endif
      DArray<int>::fromIterator(getRangeIterator(0, (int)env.signature->functions())),
      DArray<int>::fromIterator(getRangeIterator(0, (int)env.signature->typeCons())),
      DArray<int>::fromIterator(getRangeIterator(0, (int)env.signature->predicates())),
      predLevels(),
      false);
}

void KBO::zeroWeightForMaximalFunc() {
  // actually, it's non-constant maximal func, as constants cannot be weight 0

  using FunctionSymbol = unsigned;
  auto nFunctions = _funcWeights._weights.size();
  if (!nFunctions) {
    return;
  }

  FunctionSymbol maxFn = 0;
  for (FunctionSymbol i = 1; i < nFunctions; i++) {
    if (compareFunctionPrecedences(maxFn, i) == LESS) {
      maxFn = i;
    }
  }

  auto symb = env.signature->getFunction(maxFn);
  auto arity = symb->numTermArguments();

  // skip constants here (they mustn't be lighter than $var)
  if (arity != 0){
    _funcWeights._weights[maxFn] = 0;
  }
}

template<class HandleError>
void KBO::checkAdmissibility(HandleError handle) const 
{
  using FunctionSymbol = unsigned;
  auto nFunctions = _funcWeights._weights.size();

  FunctionSymbol maxFn = 0; // only properly initialized when (nFunctions > 0)
  for (FunctionSymbol i = 1; i < nFunctions; i++) {
    if (compareFunctionPrecedences(maxFn, i) == LESS) {
      maxFn = i;
    }
  }

  // TODO remove unary minus check once new 
  // theory calculus goes into master
  auto isUnaryMinus = [](unsigned functor){
    return theory->isInterpretedFunction(functor, IntTraits::minusI) ||
           theory->isInterpretedFunction(functor, RatTraits::minusI) ||
           theory->isInterpretedFunction(functor, RealTraits::minusI);
  };

  ////////////////// check kbo-releated constraints //////////////////
  unsigned varWght = _funcWeights._specialWeights._variableWeight;

  for (unsigned i = 0; i < nFunctions; i++) {
    auto arity = env.signature->getFunction(i)->numTermArguments();

    if (_funcWeights._weights[i] < varWght && arity == 0) {
      handle(UserErrorException("weight of constants (i.e. ", env.signature->getFunction(i)->name(), ") must be greater or equal to the variable weight (", varWght, ")"));

    } else if (_funcWeights.symbolWeight(i) == 0 && arity == 1 && maxFn != i && !isUnaryMinus(i)) {
      handle(UserErrorException( "a unary function of weight zero (i.e.: ", env.signature->getFunction(i)->name(), ") must be maximal wrt. the precedence ordering"));

    }
  }

  if (_funcWeights._introducedSymbolWeight < varWght) {
    handle(UserErrorException("weight of introduced function symbols must be greater than the variable weight (= ", varWght, "), since there might be new constant symbols introduced during proof search."));
  }


  if ( _funcWeights._specialWeights._numReal < varWght
    || _funcWeights._specialWeights._numInt  < varWght
    || _funcWeights._specialWeights._numRat  < varWght
      ) {
    handle(UserErrorException("weight of (number) constant symbols must be >= variable weight (", varWght, ")."));
  }

  if (varWght <= 0) {
    handle(UserErrorException("variable weight must be greater than zero"));
  }
}


/**
 * Create a KBO object.
 */
KBO::KBO(Problem& prb, const Options& opts)
 : PrecedenceOrdering(prb, opts)
 , _funcWeights(weightsFromOpts<FuncSigTraits>(opts,_functionPrecedences))
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
 , _predWeights(weightsFromOpts<PredSigTraits>(opts,_predicatePrecedences))
#endif
 , _state(new State(this))
 , _stateGt(new StateGreater(this))
 , _stateGtVo(new StateGreaterVO(this))
 , _stateGtSubst(new StateGreaterSubst(this))
{
  if (opts.kboMaxZero()) {
    zeroWeightForMaximalFunc();
  }

  if (opts.kboAdmissabilityCheck() == Options::KboAdmissibilityCheck::ERROR)
    checkAdmissibility(throwError);
  else
    checkAdmissibility(warnError);
}

KBO::~KBO()
{
  delete _state;
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::comparePredicates(Literal* l1, Literal* l2) const
{
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  Result res;
  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif
  state->init();
  if(p1!=p2) {
    TermList* ts;
    ts=l1->args();
    while(!ts->isEmpty()) {
      state->traverse(*ts,1);
      ts=ts->next();
    }
    ts=l2->args();
    while(!ts->isEmpty()) {
      state->traverse(*ts,-1);
      ts=ts->next();
    }
  } else {
    state->traverse(l1,l2);
  }

  res=state->result(l1,l2);
#if VDEBUG
  _state=state;
#endif
  return res;
} // KBO::comparePredicates()

Ordering::Result KBO::compare(TermList tl1, TermList tl2) const
{
  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
  }
  if(tl2.isOrdinaryVar()) {
    return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  ASS(_state);
  State* state=_state;
#if VDEBUG
  //this is to make sure _state isn't used while we're using it
  _state=0;
#endif

  state->init();
  if(t1->functor()==t2->functor()) {
    state->traverse(t1,t2);
  } else {
    state->traverse(tl1,1);
    state->traverse(tl2,-1);
  }
  Result res=state->result(t1,t2);
#if VDEBUG
  _state=state;
#endif
  return res;
}

bool canDecomposeIntoConstraints(TermList lhs, TermList rhs)
{
  TIME_TRACE("canDecomposeIntoConstraints");
  if (lhs.isVar()) {
    if (rhs.isVar()) {
      return true;
    }
    return false;
  }
  if (rhs.isVar() || !TermList::sameTopFunctor(lhs,rhs)) {
    return false;
  }
  auto t0 = lhs.term();
  auto t1 = rhs.term();
  for (unsigned i = 0; i < t0->arity(); i++) {
    if (!canDecomposeIntoConstraints(*t0->nthArgument(i),*t1->nthArgument(i))) {
      return false;
    }
  }
  return true;
}

bool KBO::weightsOk(TermList lhs, TermList rhs) const
{
  if (lhs == rhs) {
    return true;
  }
  if (lhs.isVar() || rhs.isVar()) {
    return false;
  }
  auto t0 = lhs.term();
  auto t1 = rhs.term();
  computeWeight(t0);
  computeWeight(t1);

  if (t0->kboWeight()!=t1->kboWeight()) {
    return false;
  }

  DHMap<unsigned, unsigned> varDiffs;
  VariableIterator vit0(t0);
  while (vit0.hasNext()) {
    auto v = vit0.next();
    unsigned* ptr;
    varDiffs.getValuePtr(v.var(),ptr,0);
    (*ptr)++;
  }
  VariableIterator vit1(t1);
  while (vit1.hasNext()) {
    auto v = vit1.next();
    unsigned* ptr;
    if (varDiffs.getValuePtr(v.var(),ptr,0)) {
      return false;
    }
    if (*ptr == 0) {
      return false;
    }
    (*ptr)--;
  }
  DHMap<unsigned, unsigned>::Iterator vdIt(varDiffs);
  while (vdIt.hasNext()) {
    if (vdIt.next()!=0) {
      return false;
    }
  }
  return true;
}

bool KBO::isGreater(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, const Indexing::TermQueryResult* qr) const
{
  // ASS_REP(!constraints || *constraints, *constraints);
  TIME_TRACE("KBO::isGreater");
  static DHMap<Literal*,bool> weightsOkCache;
  bool weightsOkFlag = false;
  if (qr) {
    auto lhs = qr->term;
    auto rhs = EqHelper::getOtherEqualitySide(qr->literal, lhs);
    auto eqOrd = getEqualityArgumentOrder(qr->literal);
    if (eqOrd==GREATER) {
      ASS_EQ(lhs,*qr->literal->nthArgument(0));
      return true;
    } else if (eqOrd==LESS) {
      ASS_EQ(lhs,*qr->literal->nthArgument(1));
      return true;
    }

    bool* woPtr;
    if (weightsOkCache.getValuePtr(qr->literal, woPtr)) {
      *woPtr = weightsOk(lhs,rhs);
    }
    weightsOkFlag = *woPtr;

  //   DemodulatorConstraints* dc;
  //   if (_demodulatorCache.getValuePtr(make_pair(qr->term,qr->literal),dc)) {
  //     dc->canDecompose = canDecomposeIntoConstraints(lhs,rhs);
  //     if (dc->canDecompose) {
  //       NEVER(isGreater(lhs,rhs,nullptr,&dc->constraints,nullptr));
  //       cout << "constraints for " << lhs << " = " << rhs << endl;
  //       for (const auto& c : dc->constraints) {
  //         auto x = get<0>(c);
  //         auto y = get<1>(c);
  //         auto strict = get<2>(c);
  //         cout << "X" << x << (strict?" > X":" >= X") << y << endl;
  //       }
  //       cout << "also: " << endl;
  //       Stack<VarOrder> vos;
  //       vos.push(VarOrder());
  //       while (vos.isNonEmpty()) {
  //         auto vo = vos.pop();
  //         VarOrder ext = vo;
  //         if (makeGreater(lhs,rhs,ext)) {
  //           cout << ext.to_string() << endl;
  //           for (auto&& diff : VarOrder::order_diff(vo,ext)) {
  //             vos.push(std::move(diff));
  //           }
  //         }
  //       }
  //       cout << endl;
  //     }
  //   }
  //   if (dc->canDecompose) {
  //     for (const auto& c : dc->constraints) {
  //       auto xS = qr->substitution->applyToBoundResult(get<0>(c));
  //       auto yS = qr->substitution->applyToBoundResult(get<1>(c));
  //       auto strict = get<2>(c);
  //       if (!strict && xS == yS) {
  //         return true;
  //       }
  //       Stack<std::tuple<unsigned,unsigned,bool>> localC;
  //       if (isGreater(xS,yS,nullptr,&localC,nullptr)) {
  //         return true;
  //       }
  //       if (constraints) {
  //         for (const auto& c : localC) {
  //           constraints->push(c);
  //         }
  //       }
  //     }
  //     // if (isGreater(tl1,qr->substitution->applyToBoundResult(tl2),nullptr,constraints,nullptr)) {
  //     //   TIME_TRACE("nope");
  //     //   return true;
  //     //   // cout << tl1 << " should be greater than " << qr->substitution->applyToBoundResult(tl2) << endl;
  //     //   // cout << "coming from " << lhs << " = " << rhs << endl << endl;
  //     // }
  //     // for now just return here if we didn't find a suitable constraint
  //     return false;
  //   }
  }
  Indexing::ResultSubstitution* subst = qr ? qr->substitution.ptr() : nullptr;
  VarOrderBV newConstraints = 0;

  auto res = subst
    ? isGreaterHelper(tl1,tl2, tl1State, constraints, constraints ? &newConstraints : nullptr, subst, weightsOkFlag)
    : isGreaterHelper(tl1,tl2, tl1State, constraints, constraints ? &newConstraints : nullptr);
  // if (subst && (compare(tl1,subst->applyToBoundResult(tl2))==Ordering::GREATER)!=res) {
  //   cout << tl1.toString()+" "+tl2.toString()+" applied "+subst->applyToBoundResult(tl2).toString()+" false "+(res?"positive":"negative") << endl;
  // }
#if VDEBUG
  auto tl2S = subst?subst->applyToBoundResult(tl2):tl2;
  ASS_REP((compare(tl1,tl2S)==Ordering::GREATER)==res,
    tl1.toString()+" "+tl2S.toString()+" (orig "+tl2.toString()+") false "+(res?"positive":"negative"));

  if (res) {
    newConstraints = 0;
  }

  if (!res && constraints) {
    for (unsigned i = 0; i < 6; i++) {
      for (unsigned j = i+1; j <= 6; j++) {

        // TODO the assertions below could be strenthened into equivalences, i.e. we could have more constraints

        VarOrder vo_gt;
        vo_gt.add_gt(i,j);
        auto bit_gt = isBitSet(i,j,PoComp::GT,*constraints);
        auto new_bit_gt = isBitSet(i,j,PoComp::GT,newConstraints);
        auto isGreater_gt = isGreater(tl1,tl2S,vo_gt);
        ASS(bit_gt || !new_bit_gt);
        ASS_REP(!bit_gt || !new_bit_gt || isGreater_gt,
          tl1.toString()+"\n"+tl2S.toString()+"\n (orig "+tl2.toString()+") under "+vo_gt.to_string());

        VarOrder vo_lt;
        vo_lt.add_gt(j,i);
        auto bit_lt = isBitSet(i,j,PoComp::LT,*constraints);
        auto new_bit_lt = isBitSet(i,j,PoComp::LT,newConstraints);
        auto isGreater_lt = isGreater(tl1,tl2S,vo_lt);
        ASS(bit_lt || !new_bit_lt);
        ASS_REP(!bit_lt || !new_bit_lt || isGreater_lt,
          tl1.toString()+"\n"+tl2S.toString()+"\n (orig "+tl2.toString()+") under "+vo_lt.to_string());

        VarOrder vo_eq;
        vo_eq.add_eq(i,j);
        VarOrder::EqApplicator voApp(vo_eq);
        auto bit_eq = isBitSet(i,j,PoComp::EQ,*constraints);
        auto new_bit_eq = isBitSet(i,j,PoComp::EQ,newConstraints);
        auto isGreater_eq = isGreater(SubstHelper::apply(tl1,voApp),SubstHelper::apply(tl2S,voApp),vo_eq);
        ASS(bit_eq || !new_bit_eq);
        ASS_REP(!bit_eq || !new_bit_eq || isGreater_eq,
          tl1.toString()+"\n"+tl2S.toString()+"\n (orig "+tl2.toString()+") under "+vo_eq.to_string());
      }
    }
  }
#endif
  if (constraints) {
    *constraints = newConstraints;
  }
  ASS(!constraints || *constraints!=~0UL);
  return res;
}

bool KBO::isGreaterHelper(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, VarOrderBV* newConstraints) const
{
  if (tl1==tl2) {
    return false;
  }
  if (tl1.isOrdinaryVar()) {
    // if (constraints && tl2.isOrdinaryVar()) {
    //   if (isBitSet(tl1.var(),tl2.var(),PoComp::GT,*constraints)) {
    //     TIME_TRACE("setting bit here");
    //     setBit(tl1.var(),tl2.var(),PoComp::GT,*newConstraints);
    //   }
    // }
    return false;
  }
  if(tl2.isOrdinaryVar()) {
    if (tl1.isTerm() && tl1.containsSubterm(tl2)) {
      return true;
    }
    // for (unsigned i = 0; i <= 6; i++) {
    //   if (i == tl2.var() || !(tl1.term()->varmap() & (1 << i))) {
    //     continue;
    //   }
    //   if (isBitSet(i,tl2.var(),PoComp::GT,*constraints)) {
    //     TIME_TRACE("setting bit here");
    //     setBit(i,tl2.var(),PoComp::GT,*newConstraints);
    //   }
    //   if (isBitSet(i,tl2.var(),PoComp::EQ,*constraints)) {
    //     TIME_TRACE("setting bit here");
    //     setBit(i,tl2.var(),PoComp::EQ,*newConstraints);
    //   }
    // }
    return false;
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  if ((~t1->varmap() & t2->varmap()) || t1->numVarOccs() < t2->numVarOccs()) {
    return false;
  }

  computeWeight(t1);
  computeWeight(t2);

  if (t1->kboWeight()<t2->kboWeight()) {
    return false;
  }

  auto s = static_cast<LeftState*>(tl1State);
  ASS(!s || s->t==t1);

  _stateGt->init();
  _stateGt->setConstraints(constraints,newConstraints);
  if (t1->kboWeight()>t2->kboWeight()) {
    // traverse variables
    if (s) {
      if (s->ready) {
        _stateGt->init(s);
      } else {
        _stateGt->traverseVars(tl1,1);
        _stateGt->initState(s);
      }
    } else {
      _stateGt->traverseVars(tl1,1);
    }
    _stateGt->traverseVars(tl2,-1);
    return _stateGt->checkVars();
  }
  // t1->kboWeight()==t2->kboWeight()
  Result comp = t1->isSort()
    ? compareTypeConPrecedences(t1->functor(),t2->functor())
    : compareFunctionPrecedences(t1->functor(),t2->functor());
  switch (comp)
  {
    case Ordering::LESS:
    case Ordering::LESS_EQ: {
      return false;
    }
    case Ordering::GREATER:
    case Ordering::GREATER_EQ: {
      if (s) {
        if (s->ready) {
          _stateGt->init(s);
        } else {
          _stateGt->traverseVars(tl1,1);
          _stateGt->initState(s);
        }
      } else {
        _stateGt->traverseVars(tl1,1);
      }
      _stateGt->traverseVars(tl2,-1);
      return _stateGt->checkVars();
    }
    case Ordering::EQUAL: {
      return _stateGt->traverse(t1,t2);
    }
    case Ordering::INCOMPARABLE:
      ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
}

bool KBO::isGreaterHelper(TermList tl1, TermList tl2, void* tl1State, VarOrderBV* constraints, VarOrderBV* newConstraints, Indexing::ResultSubstitution* subst, bool weightsEqual) const
{
  ASS(subst);
  if (tl2.isOrdinaryVar()) {
    ASS(!weightsEqual);
    return isGreaterHelper(tl1,subst->applyToBoundResult(tl2.var()),nullptr,constraints,newConstraints);
  }
  if (tl1.isOrdinaryVar()) {
    return false;
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  auto s = static_cast<LeftState*>(tl1State);
  ASS(!s || s->t==t1);
  _stateGtSubst->init(subst);
  _stateGtSubst->setConstraints(constraints,newConstraints);

  if (!weightsEqual) {
    computeWeight(t1);
    computeWeight2(t2,subst);

    if (t1->kboWeight()<t2->kboWeight2()) {
      return false;
    }

    if (t1->kboWeight()>t2->kboWeight2()) {
      // traverse variables
      if (s) {
        if (s->ready) {
          _stateGtSubst->init(s,subst);
        } else {
          _stateGtSubst->traverseVars(tl1,1);
          _stateGtSubst->initState(s);
        }
      } else {
        _stateGtSubst->traverseVars(tl1,1);
      }
      _stateGtSubst->traverseVars2(tl2);
      return _stateGtSubst->checkVars();
    }
  }
  // t1->kboWeight()==t2->kboWeight()
  Result comp = t1->isSort()
    ? compareTypeConPrecedences(t1->functor(),t2->functor())
    : compareFunctionPrecedences(t1->functor(),t2->functor());
  switch (comp)
  {
    case Ordering::LESS:
    case Ordering::LESS_EQ: {
      return false;
    }
    case Ordering::GREATER:
    case Ordering::GREATER_EQ: {
      if (s) {
        if (s->ready) {
          _stateGtSubst->init(s,subst);
        } else {
          _stateGtSubst->traverseVars(tl1,1);
          _stateGtSubst->initState(s);
        }
      } else {
        _stateGtSubst->traverseVars(tl1,1);
      }
      _stateGtSubst->traverseVars2(tl2);
      return _stateGtSubst->checkVars();
    }
    case Ordering::EQUAL: {
      return _stateGtSubst->traverse(t1,t2,weightsEqual);
    }
    case Ordering::INCOMPARABLE:
      ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
}

bool KBO::isGreater(TermList tl1, TermList tl2, const VarOrder& vo) const
{
  TIME_TRACE("KBO:isGreater2");
  if (tl1 == tl2) {
    return false;
  }
  if (tl1.isVar()) {
    if (tl2.isVar()) {
      return vo.query(tl1.var(),tl2.var()) == PoComp::GT;
    }
    return false;
  }
  if (tl2.isVar()) {
    VariableIterator vit(tl1.term());
    while (vit.hasNext()) {
      auto v = vit.next().var();
      if (v == tl2.var() || vo.query(v,tl2.var()) == PoComp::GT) {
        return true;
      }
    }
    return false;
  }

  auto t1 = tl1.term();
  auto t2 = tl2.term();

  computeWeight(t1);
  computeWeight(t2);

  if (t1->kboWeight()<t2->kboWeight()) {
    return false;
  }
  if (t1->kboWeight()==t2->kboWeight()) {
    if (t1->functor()==t2->functor()) {
      // lexicographic case
      bool gt = false;
      for (unsigned i = 0; i < t1->arity(); i++) {
        auto arg1 = *t1->nthArgument(i);
        auto arg2 = *t2->nthArgument(i);
        if (arg1 == arg2) {
          continue;
        }
        if (isGreater(arg1,arg2,vo)) {
          ASS_REP(!vo.is_empty() || compare(arg1,arg2)==Ordering::GREATER, vstring("lex ") + arg1.toString() + " not greater than " + arg2.toString());
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
        if (compareTypeConPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
          return false;
        }
      } else {
        if (compareFunctionPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
          return false;
        }
      }
    }
  }
  // if (t2->numVarOccs()>t1->numVarOccs()) {
  //   return false;
  // }

  // compare variables
  VariableIterator vit2(t2);
  DHMap<unsigned,unsigned> varCnts;
  while (vit2.hasNext()) {
    unsigned* cnt;
    varCnts.getValuePtr(vit2.next().var(), cnt, 0);
    (*cnt)++;
  }

  VariableIterator vit1(t1);
  unsigned pos = varCnts.size();
  while (vit1.hasNext()) {
    unsigned t1v = vit1.next().var();
    DHMap<unsigned,unsigned>::Iterator vit2(varCnts);
    while (vit2.hasNext()) {
      unsigned t2v;
      unsigned& cnt = vit2.nextRef(t2v);
      if (t1v == t2v || vo.query(t1v,t2v) == PoComp::GT) {
        if (!cnt) { // already 0
          continue;
        }
        cnt--;
        if (!cnt) {
          ASS(pos);
          pos--;
        }
        // break; // this particular variable occurrence cannot be used anymore
      }
    }
  }
  if (pos) {
    // cout << "compare " << tl1 << " " << tl2 << endl;
    return false;
  }

  return true;
}

bool KBO::makeGreater(TermList tl1, TermList tl2, VarOrder& vo) const
{
  TIME_TRACE("KBO::makeGreater");
  // cout << "makeGreater " << tl1 << " " << tl2 << " under " << vo.to_string() << endl;
  if (makeGreaterRecursive(tl1,tl2,vo)) {
#if VDEBUG
    VarOrder::EqApplicator voApp(vo);
    ASS_REP(isGreater(
      SubstHelper::apply(tl1,voApp),
      SubstHelper::apply(tl2,voApp),
      vo),tl1.toString()+" "+tl2.toString()+" "+vo.to_string());
#endif
    return true;
  }
  return false;
}

bool KBO::makeGreaterNonRecursive(TermList tl1, TermList tl2, VarOrder& vo) const
{
  TIME_TRACE("KBO::makeGreaterNonRecursive");
  if (tl1 == tl2) {
    return false;
  }
  if (tl1.isVar()) {
    return tl2.isVar() && vo.add_gt(tl1.var(),tl2.var());
  }
  if (tl2.isVar()) {
    int inc = -1;
    VariableIterator vit(tl1.term());
    while (vit.hasNext()) {
      auto v = vit.next().var();
      auto c = vo.query(v,tl2.var());
      if (c == PoComp::EQ || c == PoComp::GT) {
        return true;
      } else if (c == PoComp::INC && inc == -1) {
        inc = v;
      }
    }
    if (inc != -1) {
      ALWAYS(vo.add_gt(inc,tl2.var()));
      return true;
    }
    return false;
  }

  auto t1 = tl1.term();
  auto t2 = tl2.term();

  computeWeight(t1);
  computeWeight(t2);

  if (t1->kboWeight()<t2->kboWeight()) {
    return false;
  }
  _stateGtVo->init();
  if (t1->kboWeight()>t2->kboWeight()) {
    // traverse variables
    _stateGtVo->traverseVars(tl1,true/*left*/,vo);
    _stateGtVo->traverseVars(tl2,false/*left*/,vo);
    return _stateGtVo->checkVars(vo);
  }
  // t1->kboWeight()==t2->kboWeight()
  Result comp = t1->isSort()
    ? compareTypeConPrecedences(t1->functor(),t2->functor())
    : compareFunctionPrecedences(t1->functor(),t2->functor());
  switch (comp)
  {
    case Ordering::LESS:
    case Ordering::LESS_EQ: {
      return false;
    }
    case Ordering::GREATER:
    case Ordering::GREATER_EQ: {
      _stateGtVo->traverseVars(tl1,true/*left*/,vo);
      _stateGtVo->traverseVars(tl2,false/*left*/,vo);
      return _stateGtVo->checkVars(vo);
    }
    case Ordering::EQUAL: {
      return _stateGtVo->traverse(t1,t2,vo);
    }
    case Ordering::INCOMPARABLE:
      ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
}

bool KBO::makeGreaterRecursive(TermList tl1, TermList tl2, VarOrder& vo) const
{
  TIME_TRACE("KBO::makeGreaterRecursive");
  if (tl1 == tl2) {
    return false;
  }
  if (tl1.isVar()) {
    if (tl2.isVar()) {
      return vo.add_gt(tl1.var(),tl2.var());
    }
    return false;
  }
  if (tl2.isVar()) {
    int inc = -1;
    VariableIterator vit(tl1.term());
    while (vit.hasNext()) {
      auto v = vit.next().var();
      auto c = vo.query(v,tl2.var());
      if (c == PoComp::EQ || c == PoComp::GT) {
        return true;
      } else if (c == PoComp::INC && inc == -1) {
        inc = v;
      }
    }
    if (inc != -1) {
      ALWAYS(vo.add_gt(inc,tl2.var()));
      return true;
    }
    return false;
  }

  auto t1 = tl1.term();
  auto t2 = tl2.term();

  computeWeight(t1);
  computeWeight(t2);

  if (t1->kboWeight()<t2->kboWeight()) {
    return false;
  }
  if (t1->kboWeight()==t2->kboWeight()) {
    if (t1->functor()==t2->functor()) {
      // lexicographic case
      bool gt = false;
      for (unsigned i = 0; i < t1->arity(); i++) {
        auto arg1 = *t1->nthArgument(i);
        auto arg2 = *t2->nthArgument(i);
        if (arg1 == arg2) {
          continue;
        }
        if (makeGreaterRecursive(arg1,arg2,vo)) {
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
        if (compareTypeConPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
          return false;
        }
      } else {
        if (compareFunctionPrecedences(t1->functor(),t2->functor()) != Ordering::GREATER) {
          return false;
        }
      }
    }
  }
  // cout << "compare vars of " << *t1 << " and " << *t2 << endl;

  // compare variables
  VariableIterator vit2(t2);
  DHMap<unsigned,unsigned> varCnts;
  while (vit2.hasNext()) {
    unsigned* cnt;
    auto v = vit2.next();
    varCnts.getValuePtr(v.var(), cnt, 0);
    (*cnt)++;
    // cout << "found " << v << " " << *cnt << endl;
  }
  // cout << "vo " << vo.to_string() << endl;

  VariableIterator vit1(t1);
  unsigned pos = varCnts.size();
  DHMap<unsigned,unsigned> varCntsExtra;
  while (vit1.hasNext()) {
    unsigned t1v = vit1.next().var();
    unsigned* cnt;
    varCntsExtra.getValuePtr(t1v, cnt, 0);
    (*cnt)++;
    // cout << "found2 " << t1v << " " << *cnt << endl;

    DHMap<unsigned,unsigned>::Iterator vit2(varCnts);
    while (vit2.hasNext()) {
      unsigned t2v;
      unsigned& cnt2 = vit2.nextRef(t2v);
      // cout << "remaining of X" << t2v << " " << cnt2 << endl;
      if (t1v == t2v || vo.query(t1v,t2v) == PoComp::GT) {
        if (!cnt2) { // already 0
          continue;
        }
        // cout << "decreased" << endl;
        cnt2--;
        if (!cnt2) {
          ASS(pos);
          pos--;
        }
      }
    }
  }
  if (pos) {
    // TODO try to find more variables
    DHMap<unsigned,unsigned>::Iterator vit2(varCnts);
    while (vit2.hasNext() && pos) {
      unsigned t2v;
      unsigned& cnt2 = vit2.nextRef(t2v);
      if (cnt2) {
        DHMap<unsigned,unsigned>::Iterator vit1(varCntsExtra);
        while (vit1.hasNext() && cnt2) {
          unsigned t1v;
          unsigned cnt1;
          vit1.next(t1v,cnt1);
          if (vo.query(t1v,t2v)==PoComp::INC && vo.add_gt(t1v,t2v)) {
            if (cnt2 < cnt1) {
              cnt2 = 0;
              break;
            } else {
              cnt2 -= cnt1;
            }
          }
        }
        if (!cnt2) {
          pos--;
        }
      }
    }
    if (!pos) {
      TIME_TRACE("fixed order");
    }
    return !pos;
  }

  return true;
}

void* KBO::createState() const
{
  return new LeftState;
}

void KBO::initStateForTerm(void* state, Term* t) const
{
  ASS(state);
  static_cast<LeftState*>(state)->t = t;
  static_cast<LeftState*>(state)->ready = false;
  static_cast<LeftState*>(state)->varCnts.reset();
}

void KBO::destroyState(void* state) const
{
  delete static_cast<LeftState*>(state);
}

int KBO::symbolWeight(Term* t) const
{
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  if (t->isLiteral()) 
    return _predWeights.symbolWeight(t);
  else 
#endif
  if (t->isSort()){
    //For now just give all type constructors minimal weight
    return _funcWeights._specialWeights._variableWeight;
  }
  return _funcWeights.symbolWeight(t);
}

void KBO::computeWeight(Term* t) const
{
  if (t->kboWeight()!=-1) {
    return;
  }
  struct Todo {
    Term* t;
    unsigned w;
    TermList* args;
  };
  static Stack<Todo> stack(8);
  stack.push(Todo {
    .t = t,
    .w = (unsigned)symbolWeight(t),
    .args = t->args(),
  });

  while (stack.isNonEmpty()) {
    auto& curr = stack.top();
    if (curr.args->isEmpty()) {
      stack.pop();
      if (stack.isNonEmpty()) {
        stack.top().w += curr.w;
      }
      curr.t->setKboWeight(curr.w);
      continue;
    }
    auto arg = curr.args;
    // update this here so reallocation won't affect it
    curr.args = curr.args->next();
    if (arg->isVar()) {
      stack.top().w += _funcWeights._specialWeights._variableWeight;
    } else {
      auto w = arg->term()->kboWeight();
      if (w!=-1) {
        stack.top().w += w;
      } else {
        stack.push(Todo{
          .t = arg->term(),
          .w = (unsigned)symbolWeight(arg->term()),
          .args = arg->term()->args()
        });
      }
    }
  }
  ASS(stack.isEmpty());
  ASS_NEQ(t->kboWeight(),-1);
}

void KBO::computeWeight2(Term* t, Indexing::ResultSubstitution* subst) const
{
  struct Todo {
    Term* t;
    unsigned w;
    TermList* args;
  };
  static Stack<Todo> stack(8);
  stack.push(Todo {
    .t = t,
    .w = (unsigned)symbolWeight(t),
    .args = t->args(),
  });
  static int ts = 0;
  ts++;

  while (stack.isNonEmpty()) {
    auto& curr = stack.top();
    if (curr.args->isEmpty()) {
      stack.pop();
      if (stack.isNonEmpty()) {
        stack.top().w += curr.w;
      }
      curr.t->setKboWeight2(curr.w);
      curr.t->setKboWeight2TimeStamp(ts);
      continue;
    }
    auto arg = curr.args;
    // update this here so reallocation won't affect it
    curr.args = curr.args->next();
    if (arg->isVar()) {
      auto argS = subst->applyToBoundResult(arg->var());
      if (argS.isVar()) {
        stack.top().w += _funcWeights._specialWeights._variableWeight;
      } else {
        computeWeight(argS.term());
        stack.top().w += argS.term()->kboWeight();
      }
    } else {
      auto tts = arg->term()->kboWeight2TimeStamp();
      if (tts==ts) {
        stack.top().w += arg->term()->kboWeight2();
      } else {
        stack.push(Todo{
          .t = arg->term(),
          .w = (unsigned)symbolWeight(arg->term()),
          .args = arg->term()->args()
        });
      }
      // stack.push(Todo{
      //   .t = arg->term(),
      //   .w = (unsigned)symbolWeight(arg->term()),
      //   .args = arg->term()->args()
      // });
    }
  }
  ASS(stack.isEmpty());
}

unsigned KBO::weight(TermList t) const
{
  if (t.isVar()) {
    return _funcWeights._specialWeights._variableWeight;
  }
  ASS_NEQ(t.term()->kboWeight(),-1);
  return t.term()->kboWeight();
}

unsigned KBO::weight2(TermList t, Indexing::ResultSubstitution* subst, bool underSubst) const
{
  if (underSubst) {
    return weight(t);
  }
  if (t.isVar()) {
    return weight(subst->applyToBoundResult(t.var()));
  }
  return t.term()->kboWeight2();
}

template<class SigTraits>
KboWeightMap<SigTraits> KboWeightMap<SigTraits>::dflt()
{
  return KboWeightMap {
    ._weights                = DArray<KboWeight>::initialized(SigTraits::nSymbols(), 1),
    ._introducedSymbolWeight = 1,
    ._specialWeights         = KboSpecialWeights<SigTraits>::dflt(),
  };
}

template<class SigTraits>
template<class Extractor, class Fml>
KboWeightMap<SigTraits> KboWeightMap<SigTraits>::fromSomeUnsigned(Extractor ex, Fml fml)
{
  auto nSym = SigTraits::nSymbols();
  DArray<KboWeight> weights(nSym);

  decltype(ex(0)) max = 0;
  for (unsigned i = 0; i < nSym; i++) {
    auto a = ex(i);
    if (a > max) {
      max = a;
    }
  }

  for (unsigned i = 0; i < nSym; i++) {
    weights[i] = fml(max,ex(i));
  }

  return KboWeightMap {
    ._weights                = weights,
    ._introducedSymbolWeight = 1,
    ._specialWeights         = KboSpecialWeights<SigTraits>::dflt(),
  };
}


template<>
template<class Random>
KboWeightMap<FuncSigTraits> KboWeightMap<FuncSigTraits>::randomized(unsigned maxWeight, Random random)
{
  using SigTraits = FuncSigTraits;
  auto nSym = SigTraits::nSymbols();

  unsigned variableWeight   = 1;
  unsigned introducedWeight = random(variableWeight, maxWeight);
  unsigned numInt           = random(variableWeight, maxWeight);
  unsigned numRat           = random(variableWeight, maxWeight);
  unsigned numReal          = random(variableWeight, maxWeight);

  DArray<KboWeight> weights(nSym);
  for (unsigned i = 0; i < nSym; i++) {
    if (SigTraits::isConstantSymbol(i)) {
      weights[i] = random(variableWeight, maxWeight);
    } else if (SigTraits::isUnaryFunction(i)) {
      // TODO support one zero-weight-unary-function per sort
      weights[i] = random(1, maxWeight); 
    } else {
      weights[i] = random(0, maxWeight);
    }
  }

  return KboWeightMap {
    ._weights                = weights,
    ._introducedSymbolWeight = introducedWeight,
    ._specialWeights         = KboSpecialWeights<FuncSigTraits> {
      ._variableWeight = variableWeight,
      ._numInt     =  numInt,
      ._numRat     =  numRat,
      ._numReal    =  numReal,
    },
  };
}

template<class SigTraits>
KboWeightMap<SigTraits> KboWeightMap<SigTraits>::randomized()
{ return randomized(1 << 16, [](unsigned min, unsigned max) { return min + Random::getInteger(max - min); }); }

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
template<>
template<class Random>
KboWeightMap<PredSigTraits> KboWeightMap<PredSigTraits>::randomized(unsigned maxWeight, Random random)
{
  using SigTraits = FuncSigTraits;
  auto nSym = SigTraits::nSymbols();

  unsigned introducedWeight = random(0, maxWeight);

  DArray<KboWeight> weights(nSym);
  for (unsigned i = 0; i < nSym; i++) {
    weights[i] = random(0, maxWeight);
  }

  return KboWeightMap {
    ._weights                = weights,
    ._introducedSymbolWeight = introducedWeight,
    ._specialWeights         = KboSpecialWeights<PredSigTraits>{},
  };
}
#endif

template<class SigTraits>
KboWeight KboWeightMap<SigTraits>::symbolWeight(Term* t) const
{
  return symbolWeight(t->functor());
}

template<class SigTraits>
KboWeight KboWeightMap<SigTraits>::symbolWeight(unsigned functor) const
{

  unsigned weight;
  if (!_specialWeights.tryGetWeight(functor, weight)) {
    weight = functor < _weights.size() ? _weights[functor]
                                       : _introducedSymbolWeight;
  }
  return weight;
}

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
void showSpecialWeights(const KboSpecialWeights<PredSigTraits>& ws, ostream& out) 
{ }
#endif

void showSpecialWeights(const KboSpecialWeights<FuncSigTraits>& ws, ostream& out) 
{ 
  out << "% " SPECIAL_WEIGHT_IDENT_VAR        " " << ws._variableWeight         << std::endl;
  out << "% " SPECIAL_WEIGHT_IDENT_NUM_REAL   " " << ws._numReal                << std::endl;
  out << "% " SPECIAL_WEIGHT_IDENT_NUM_RAT    " " << ws._numRat                 << std::endl;
  out << "% " SPECIAL_WEIGHT_IDENT_NUM_INT    " " << ws._numInt                 << std::endl;
}
template<class SigTraits>
void KBO::showConcrete_(ostream& out) const  
{
  out << "% Weights of " << SigTraits::symbolKindName() << " (line format: `<name> <arity> <weight>`)" << std::endl;
  out << "% ===== begin of " << SigTraits::symbolKindName() << " weights ===== " << std::endl;
  

  auto& map = getWeightMap<SigTraits>();
  DArray<unsigned> functors;
  functors.initFromIterator(getRangeIterator(0u,SigTraits::nSymbols()),SigTraits::nSymbols());
  functors.sort(closureComparator([&](unsigned l, unsigned r) { return Int::compare(map.symbolWeight(l), map.symbolWeight(r)); }));

  for (unsigned i = 0; i < SigTraits::nSymbols(); i++) {
    auto functor = functors[i];
    auto sym = SigTraits::getSymbol(functor);
    out << "% " << sym->name() << " " << sym->arity() << " " << map.symbolWeight(functor) << std::endl;
  }

  auto& ws = getWeightMap<SigTraits>();
  out << "% " SPECIAL_WEIGHT_IDENT_INTRODUCED " " << ws._introducedSymbolWeight << std::endl;
  showSpecialWeights(ws._specialWeights, out);

  out << "% ===== end of " << SigTraits::symbolKindName() << " weights ===== " << std::endl;

}
void KBO::showConcrete(ostream& out) const  
{
  showConcrete_<FuncSigTraits>(out);
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
  out << "%" << std::endl;
  showConcrete_<PredSigTraits>(out);
#endif
}

template<> const KboWeightMap<FuncSigTraits>& KBO::getWeightMap<FuncSigTraits>() const 
{ return _funcWeights; }

#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
template<> const KboWeightMap<PredSigTraits>& KBO::getWeightMap<PredSigTraits>() const 
{ return _predWeights; }
#endif



#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
bool KboSpecialWeights<PredSigTraits>::tryGetWeight(unsigned functor, unsigned& weight) const
{ return false; }
#endif

bool KboSpecialWeights<FuncSigTraits>::tryGetWeight(unsigned functor, unsigned& weight) const
{
  auto sym = env.signature->getFunction(functor);
  if (sym->integerConstant())  { weight = _numInt;  return true; }
  if (sym->rationalConstant()) { weight = _numRat;  return true; }
  if (sym->realConstant())     { weight = _numReal; return true; }
  if (env.options->pushUnaryMinus()) {
    if (theory->isInterpretedFunction(functor, IntTraits ::minusI)) { weight = 0; return true; }
    if (theory->isInterpretedFunction(functor, RatTraits ::minusI)) { weight = 0; return true; }
    if (theory->isInterpretedFunction(functor, RealTraits::minusI)) { weight = 0; return true; }
  }
  return false;
}

template KboWeightMap<FuncSigTraits> KboWeightMap<FuncSigTraits>::dflt();
template KboWeight KboWeightMap<FuncSigTraits>::symbolWeight(Term*) const;
template KboWeight KboWeightMap<FuncSigTraits>::symbolWeight(unsigned) const;
#if __KBO__CUSTOM_PREDICATE_WEIGHTS__
template KboWeightMap<PredSigTraits> KboWeightMap<PredSigTraits>::dflt();
template KboWeight KboWeightMap<PredSigTraits>::symbolWeight(unsigned) const;
#endif

}