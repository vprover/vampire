/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "../Debug/Tracer.hpp"

#include "../Lib/Environment.hpp"
#include "../Lib/Comparison.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Int.hpp"
#include "../Lib/Metaiterators.hpp"

#include "Term.hpp"
#include "KBO.hpp"
#include "Signature.hpp"

namespace Kernel {

/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO::State
{
public:
  /** Initialise the state */
  State(KBO& kbo)
    : _weightDiff(0), _posNum(0), _negNum(0),
      _lexResult(EQUAL),
      _kbo(kbo)
  {}
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
  DHMap<unsigned, int, IdentityHash> _varDiffs;
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
    int prec1, prec2;
    if(t1->isLiteral()) {
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
    } else {
      prec1=_kbo.functionPrecedence(t1->functor());
      prec2=_kbo.functionPrecedence(t2->functor());
    }
    ASS_NEQ(prec1,prec2);//precedence ordering must be total
    res=(prec1>prec2)?GREATER:LESS;
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
  CALL("KBO::State::innerResult");

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
    } else {
      int prec1=_kbo.functionPrecedence(tl1.term()->functor());
      int prec2=_kbo.functionPrecedence(tl2.term()->functor());
      ASS_NEQ(prec1,prec2);//precedence ordering must be total
      res=(prec1>prec2)?GREATER:LESS;
    }
  }
  return applyVariableCondition(res);
}

void KBO::State::recordVariable(unsigned var, int coef)
{
  CALL("KBO::State::recordVariable");
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
  CALL("KBO::State::traverse(TermList...)");

  if(tl.isOrdinaryVar()) {
    _weightDiff+=_kbo._variableWeight*coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  _weightDiff+=_kbo.functionSymbolWeight(t->functor())*coef;

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
      _weightDiff+=_kbo.functionSymbolWeight(ts->term()->functor())*coef;
      if(ts->term()->arity()) {
	stack.push(ts->term()->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      _weightDiff+=_kbo._variableWeight*coef;
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

void KBO::State::traverse(Term* t1, Term* t2)
{
  CALL("KBO::State::traverse");
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



/**
 * Create a KBO object.
 *
 * Function and predicate preferences and predicate levels
 * must be initialized after calling this constructor and
 * before any comparisons using this object are being made.
 */
KBO::KBO(const Signature& sig)
  : _variableWeight(1),
    _defaultSymbolWeight(1),
    _predicates(sig.predicates()),
    _functions(sig.functions()),
    _predicateLevels(_predicates),
    _predicatePrecedences(_predicates),
    _functionPrecedences(_functions)
{
  ASS_G(_predicates, 0);
}

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::compare(Literal* l1, Literal* l2)
{
  CALL("KBO::compare(Literal*...)");
  ASS(l1->shared());
  ASS(l2->shared());

  if (l1 == l2) {
    return EQUAL;
  }

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();
  if (p1 != p2) {
    int lev1 = predicateLevel(p1);
    int lev2 = predicateLevel(p2);
    if (lev1 > lev2) {
      return GREATER;
    }
    if (lev2 > lev1) {
      return LESS;
    }
  }

  State state(*this);
  if(p1!=p2) {
    TermList* ts;
    ts=l1->args();
    while(!ts->isEmpty()) {
      state.traverse(*ts,1);
      ts=ts->next();
    }
    ts=l2->args();
    while(!ts->isEmpty()) {
      state.traverse(*ts,-1);
      ts=ts->next();
    }
  } else {
    state.traverse(l1,l2);
  }

  return state.result(l1,l2);
} // KBO::compare()

Ordering::Result KBO::compare(TermList tl1, TermList tl2)
{
  CALL("KBO::compare(TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
    }
  }
  if(tl2.isOrdinaryVar()) {
    if(existsZeroWeightUnaryFunction()) {
      NOT_IMPLEMENTED;
    } else {
      return tl1.containsSubterm(tl2) ? GREATER : INCOMPARABLE;
    }
  }

  ASS(tl1.isTerm());
  ASS(tl2.isTerm());

  Term* t1=tl1.term();
  Term* t2=tl2.term();

  State state(*this);
  if(t1->functor()==t2->functor()) {
    state.traverse(t1,t2);
  } else {
    state.traverse(tl1,1);
    state.traverse(tl2,-1);
  }
  return state.result(t1,t2);
}



/**
 * Return the predicate level. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality).
 * @since 11/05/2008 Manchester
 */
int KBO::predicateLevel (unsigned pred)
{
  return pred > _predicates ? 1 : _predicateLevels[pred];
} // KBO::predicateLevel


/**
 * Return the predicate precedence. If @b pred is less than or equal to
 * @b _predicates, then the value is taken from the array _predicatePrecedences,
 * otherwise it is defined to be @b pred (to make it greater than all
 * previously introduced predicates).
 * @since 11/05/2008 Manchester
 */
int KBO::predicatePrecedence (unsigned pred)
{
  return pred > _predicates ? (int)pred : _predicatePrecedences[pred];
} // KBO::predicatePrecedences

/**
 * Return the function precedence. If @b pred is less than or equal to
 * @b _functions, then the value is taken from the array _functionPrecedences,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality).
 * @since 11/05/2008 Manchester
 */
int KBO::functionPrecedence (unsigned fun)
{
  return fun > _functions ? (int)fun : _functionPrecedences[fun];
} // KBO::functionPrecedences


KBO* KBO::createReversedAgePreferenceConstantLevels()
{
  CALL("KBO::createReversedAgePreferenceConstantLevels");
  KBO* res=new KBO(*env.signature);
  for(unsigned i=0;i<res->_functions;i++) {
    res->_functionPrecedences[i]=i;
  }
  for(unsigned i=0;i<res->_predicates;i++) {
    res->_predicatePrecedences[i]=i;
    res->_predicateLevels[i]=1;
  }
  //equality is on the lowest level
  res->_predicateLevels[0]=0;
  return res;
}

struct FnArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->functionArity(u1),
	    env.signature->functionArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};
struct PredArityComparator
{
  Comparison compare(unsigned u1, unsigned u2)
  {
    Comparison res=Int::compare(env.signature->predicateArity(u1),
	    env.signature->predicateArity(u2));
    if(res==EQUAL) {
      res=Int::compare(u1,u2);
    }
    return res;
  }
};

KBO* KBO::createArityPreferenceConstantLevels()
{
  CALL("KBO::createArityPreferenceConstantLevels");

  KBO* res=new KBO(*env.signature);

  unsigned preds=res->_predicates;
  unsigned funcs=res->_functions;

  static DArray<unsigned> aux(32);
  if(funcs) {
    aux.initFromIterator(getRangeIterator(0u, funcs), funcs);
    aux.sort(FnArityComparator());
    for(unsigned i=0;i<funcs;i++) {
      res->_functionPrecedences[aux[i]]=i;
    }
  }

  aux.initFromIterator(getRangeIterator(0u, preds), preds);
  aux.sort(PredArityComparator());
  for(unsigned i=0;i<preds;i++) {
    res->_predicatePrecedences[aux[i]]=i;
  }

  res->_predicateLevels.init(res->_predicates, 1);

  //equality is on the lowest level
  res->_predicateLevels[0]=0;
  return res;
}

KBO* KBO::createArityPreferenceAndLevels()
{
  KBO* res=new KBO(*env.signature);

  unsigned preds=res->_predicates;
  unsigned funcs=res->_functions;

  DArray<unsigned> aux(funcs);

  aux.initFromIterator(getRangeIterator(0u, funcs), funcs);
  aux.sort(FnArityComparator());
  for(unsigned i=0;i<funcs;i++) {
    res->_functionPrecedences[aux[i]]=i;
  }

  aux.initFromIterator(getRangeIterator(0u, preds), preds);
  aux.sort(PredArityComparator());
  for(unsigned i=0;i<preds;i++) {
    res->_predicatePrecedences[aux[i]]=i;
    res->_predicateLevels[aux[i]]=i+1;
  }

  //equality is on the lowest level
  res->_predicateLevels[0]=0;
  return res;
}

}
