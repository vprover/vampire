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

struct IdHash {
  static unsigned hash(unsigned i) { return i; }
};

/**
 * Class to represent the current state of the KBO comparison.
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */
class KBO::State
{
public:
  /** Initialise the state */
  State(KBO& kbo)
    : weightDiff(0), posNum(0), negNum(0),
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
    if(posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    } else if(negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
      res=INCOMPARABLE;
    }
    return res;
  }

  int weightDiff;
  DHMap<unsigned, int, IdHash> varDiffs;
  /** Number of variables, that occur more times in the first literal */
  int posNum;
  /** Number of variables, that occur more times in the second literal */
  int negNum;
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
  if(weightDiff) {
    res=weightDiff>0 ? GREATER : LESS;
  } else if(t1->functor()!=t2->functor()) {
    int prec1, prec2;
    if(t1->isLiteral()) {
      prec1=_kbo.predicatePrecedence(t1->functor());
      prec2=_kbo.predicatePrecedence(t2->functor());
    } else {
      prec1=_kbo.functionPrecedence(t1->functor());
      prec2=_kbo.functionPrecedence(t2->functor());
    }
    if(prec1>prec2) {
      res=GREATER;
    } else {
      ASS(prec1<prec2);//precedence ordering must be total
      res=LESS;
    }
  } else {
    res=_lexResult;
  }
  res=applyVariableCondition(res);
  ASS( !t1->ground() || !t2->ground() || res!=INCOMPARABLE);
  return res;
}

Ordering::Result KBO::State::innerResult(TermList tl1, TermList tl2)
{
  //TODO: compiler gives "control reaches end of non-void function" warning
  //unless the line below is commented
  CALL("KBO::State::innerResult");

  ASS(!tl1.sameContent(&tl2));
  ASS(!TermList::sameTopFunctor(&tl1,&tl2));
  if(posNum==0 && negNum==0) {
    //all variables occur the same number of times in tl1 and tl2
    if(weightDiff) {
      return weightDiff>0 ? GREATER : LESS;
    } else {
      if(_kbo.existsZeroWeightUnaryFunction()) {
	//If tl1 or tl2 is a variable, the same variable must occur
	//also in the other term, but not in top level, as they would
	//have same content. Weights also must be the same, so the top
	//symbol has to be unary with zero weight.
	if(tl1.isVar()) {
	  return LESS;
	} else if(tl2.isVar()) {
	  return GREATER;
	}
      } else {
	if(tl1.isVar()) {
	  tl1.isVar();
	}
	ASS(!tl1.isVar());
	ASS(!tl2.isVar());
      }
      int prec1=_kbo.functionPrecedence(tl1.term()->functor());
      int prec2=_kbo.functionPrecedence(tl2.term()->functor());
      if(prec1>prec2) {
	return GREATER;
      } else {
	ASS(prec1<prec2);//precedence ordering must be total
	return LESS;
      }
    }
  } else if(posNum==0) {
    ASS(negNum>0);
    if(weightDiff) {
      return weightDiff>0 ? INCOMPARABLE : LESS;
    } else {
      //If tl1 was a variable, the same variable'd have to
      //occur also in tl2, but not in the top level, as they
      //would have the same content. However their weights are
      //the same, so there can be no other variables in tl2,
      //which is in contradiction with negNum>0.
      ASS(!tl1.isVar());
      if(!_kbo.allConstantsHeavierThanVariables()) {
	if(tl2.isVar()) {
	  //under some circumstances, we could return LESS_EQ, but it would
	  //complicate other things
	  return INCOMPARABLE;
	}
      } else {
	//If tl2 was a variable, tl1'd have to be ground, but
	//as all constants are heavier than variables, their
	//weights couldn't be equal.
	ASS(!tl2.isVar());
      }
      int prec1=_kbo.functionPrecedence(tl1.term()->functor());
      int prec2=_kbo.functionPrecedence(tl2.term()->functor());
      if(prec1>prec2) {
	return INCOMPARABLE;
      } else {
	ASS(prec1<prec2);//precedence ordering must be total
	return LESS;
      }
    }
  } else if(negNum==0) {
    ASS(posNum>0);
    if(weightDiff) {
      return weightDiff>0 ? GREATER : INCOMPARABLE;
    } else {
      //If tl2 was a variable, the same variable'd have to
      //occur also in tl1, but not in the top level, as they
      //would have the same content. However their weights are
      //the same, so there can be no other variables in tl1,
      //which is in contradiction with posNum>0.
      ASS(!tl2.isVar());
      if(!_kbo.allConstantsHeavierThanVariables()) {
	if(tl1.isVar()) {
	  //under some circumstances, we could return GREATER_EQ, but it would
	  //complicate other things
	  return INCOMPARABLE;
	}
      } else {
	//If tl1 was a variable, tl2'd have to be ground, but
	//as all constants are heavier than variables, their
	//weights couldn't be equal.
	ASS(!tl1.isVar());
      }
      int prec1=_kbo.functionPrecedence(tl1.term()->functor());
      int prec2=_kbo.functionPrecedence(tl2.term()->functor());
      if(prec1>prec2) {
	return GREATER;
      } else {
	ASS(prec1<prec2);//precedence ordering must be total
	return INCOMPARABLE;
      }
    }
  } else {
    ASS(posNum>0);
    ASS(negNum>0);
    return INCOMPARABLE;
  }
}

void KBO::State::recordVariable(unsigned var, int coef)
{
  CALL("KBO::State::recordVariable");
  ASS(coef==1 || coef==-1);

  int* pnum;
  varDiffs.getValuePtr(var,pnum,0);
  (*pnum)+=coef;
  if(coef==1) {
    if(*pnum==0) {
      negNum--;
    } else if(*pnum==1) {
      posNum++;
    }
  } else {
    if(*pnum==0) {
      posNum--;
    } else if(*pnum==-1) {
      negNum++;
    }
  }
}

void KBO::State::traverse(TermList tl,int coef)
{
  CALL("KBO::State::traverse(TermList...)");

  if(tl.isOrdinaryVar()) {
    weightDiff+=_kbo._variableWeight*coef;
    recordVariable(tl.var(), coef);
    return;
  }
  ASS(tl.isTerm());

  Term* t=tl.term();
  ASSERT_VALID(*t);

  weightDiff+=_kbo.functionSymbolWeight(t->functor())*coef;

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
      weightDiff+=_kbo.functionSymbolWeight(ts->term()->functor())*coef;
      if(ts->term()->arity()) {
	stack.push(ts->term()->args());
      }
    } else {
      ASS_METHOD(*ts,isOrdinaryVar());
      weightDiff+=_kbo._variableWeight*coef;
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

  TermList* ss=t1->args();
  TermList* tt=t2->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ss->next()->isEmpty()) {
      ASS(!tt->next()->isEmpty());
      stack.push(ss->next());
      stack.push(tt->next());
    }
    //if content is the same, neighter weightDiff nor varDiffs would change
    if(!ss->sameContent(tt)) {
      if(TermList::sameTopFunctor(ss,tt)) {
	ASS(ss->isTerm());
	ASS(tt->isTerm());
	ASS(ss->term()->arity());
	stack.push(ss->term()->args());
	stack.push(tt->term()->args());
      } else {
	traverse(*ss,1);
	traverse(*tt,-1);
	if(_lexResult==EQUAL) {
	  _lexResult=innerResult(*ss, *tt);
	  ASS(_lexResult!=EQUAL);
	  ASS(_lexResult!=GREATER_EQ);
	  ASS(_lexResult!=LESS_EQ);
	}
      }
    }
    if(stack.isEmpty()) {
      break;
    }
    tt=stack.pop();
    ss=stack.pop();
  }
}



/**
 *
 */
KBO::KBO(const Signature& sig)
  : _variableWeight(1),
    _defaultSymbolWeight(1),
    _predicates(sig.predicates()),
    _functions(sig.functions())
{
  CALL("KBO::KBO");
  ASS(_predicates);

  _predicateLevels = (int*)ALLOC_KNOWN(sizeof(int)*_predicates,
	  "KBO::levels");
  _predicatePrecedences = (int*)ALLOC_KNOWN(sizeof(int)*_predicates,
	  "KBO::predPrecedences");
  if(_functions) {
    _functionPrecedences = (int*)ALLOC_KNOWN(sizeof(int)*_functions,
	    "KBO::funPrecedences");
  }
} // KBO::KBO

KBO::~KBO()
{
  CALL("KBO::~KBO");

  DEALLOC_KNOWN(_predicateLevels,sizeof(int)*_predicates,"KBO::levels");
  DEALLOC_KNOWN(_predicatePrecedences,sizeof(int)*_predicates,"KBO::predPrecedences");
  if(_functions) {
    DEALLOC_KNOWN(_functionPrecedences,sizeof(int)*_functions,"KBO::funPrecedences");
  }
} // KBO::~KBO

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
  ASS(pred<0x7FFFFFFF);
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
  ASS(fun<0x7FFFFFFF);
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
  static Comparison compare(unsigned u1, unsigned u2)
  {
    return Int::compare(env.signature->functionArity(u1),
	    env.signature->functionArity(u2));
  }
};
struct PredArityComparator
{
  static Comparison compare(unsigned u1, unsigned u2)
  {
    return Int::compare(env.signature->predicateArity(u1),
	    env.signature->predicateArity(u2));
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
    aux.sort<FnArityComparator>();
    for(unsigned i=0;i<funcs;i++) {
      res->_functionPrecedences[aux[i]]=i;
    }
  }

  aux.initFromIterator(getRangeIterator(0u, preds), preds);
  aux.sort<PredArityComparator>();
  for(unsigned i=0;i<preds;i++) {
    res->_predicatePrecedences[aux[i]]=i;
  }

  for(unsigned i=0;i<res->_predicates;i++) {
    res->_predicateLevels[i]=1;
  }
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
  aux.sort<FnArityComparator>();
  for(unsigned i=0;i<funcs;i++) {
    res->_functionPrecedences[aux[i]]=i;
  }

  aux.initFromIterator(getRangeIterator(0u, preds), preds);
  aux.sort<PredArityComparator>();
  for(unsigned i=0;i<preds;i++) {
    res->_predicatePrecedences[aux[i]]=i;
    res->_predicateLevels[aux[i]]=i+1;
  }

  //equality is on the lowest level
  res->_predicateLevels[0]=0;
  return res;
}

}
