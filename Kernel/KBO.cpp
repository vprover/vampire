/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "../Debug/Tracer.hpp"

#include "../Lib/Environment.hpp"
#include "../Lib/DHMap.hpp"

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
  void traverse(Literal* l1, Literal* l2);
  void traverse(TermList tl,int coefficient);
  Result result(Literal* l1, Literal* l2);
private:
  void recordVariable(unsigned var, int coef);
  Result innerResult(TermList tl1, TermList tl2);

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

Ordering::Result KBO::State::result(Literal* l1, Literal* l2)
{
  Result res;
  if(weightDiff) {
    res=weightDiff>0 ? GREATER : LESS;
  } else if(l1->functor()!=l2->functor()) {
    int prec1=_kbo.predicatePrecedence(l1->functor());
    int prec2=_kbo.predicatePrecedence(l2->functor());
    if(prec1>prec2) {
      res=GREATER;
    } else {
      ASS(prec1<prec2);//precedence ordering must be total
      res=LESS;
    }
  } else {
    res=_lexResult;
  }
  if(posNum>0 && (res==LESS || res==LESS_EQ || res==EQUAL)) {
    res=INCOMPARABLE;
  } else if(negNum>0 && (res==GREATER || res==GREATER_EQ || res==EQUAL)) {
    res=INCOMPARABLE;
  }
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

void KBO::State::traverse(Literal* l1, Literal* l2)
{
  CALL("KBO::State::traverse");
  ASS(l1->functor()==l2->functor());

  weightDiff+=_kbo.predicateHeaderWeight(l1->header());
  weightDiff-=_kbo.predicateHeaderWeight(l2->header());

  TermList* ss=l1->args();
  TermList* tt=l2->args();
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
	stack.push(ss->term()->args());
	stack.push(tt->term()->args());
      } else {
	traverse(*ss,1);
	traverse(*tt,-1);
	if(_lexResult==EQUAL) {
	  _lexResult=innerResult(*ss, *tt);
	  ASS(_lexResult!=EQUAL);
	} else if(_lexResult==GREATER_EQ) {
	  ASSERTION_VIOLATION;
	  Result newRes=innerResult(*ss, *tt);
	  switch(newRes) {
	  case GREATER:
	    _lexResult=GREATER;
	    break;
	  case LESS:
	  case LESS_EQ:
	  case INCOMPARABLE:
	    _lexResult=INCOMPARABLE;
	    break;
#if VDEBUG
	  case EQUAL:
	    ASSERTION_VIOLATION;
	    break;
#endif
	  case GREATER_EQ: ;
	  }
	} else if(_lexResult==LESS_EQ) {
	  ASSERTION_VIOLATION;
	  Result newRes=innerResult(*ss, *tt);
	  switch(newRes) {
	  case LESS:
	    _lexResult=LESS;
	    break;
	  case GREATER:
	  case GREATER_EQ:
	  case INCOMPARABLE:
	    _lexResult=INCOMPARABLE;
	    break;
#if VDEBUG
	  case EQUAL:
	    ASSERTION_VIOLATION;
	    break;
#endif
	  case LESS_EQ: ;
	  }
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

  _predicateLevels = (int*)ALLOC_UNKNOWN(sizeof(int)*_predicates,
	  "KBO::levels");
  _predicatePrecedences = (int*)ALLOC_UNKNOWN(sizeof(int)*_predicates,
	  "KBO::predPrecedences");
  if(_functions) {
    _functionPrecedences = (int*)ALLOC_UNKNOWN(sizeof(int)*_functions,
	    "KBO::funPrecedences");
  }
//  _predicateLevels = (int*)ALLOC_KNOWN(sizeof(int)*_predicates,
//	  "KBO::levels");
//  _predicatePrecedences = (int*)ALLOC_KNOWN(sizeof(int)*_predicates,
//	  "KBO::predPrecedences");
//  if(_functions) {
//    _functionPrecedences = (int*)ALLOC_KNOWN(sizeof(int)*_functions,
//	    "KBO::funPrecedences");
//  }
} // KBO::KBO

KBO::~KBO()
{
  CALL("KBO::~KBO");

  DEALLOC_UNKNOWN(_predicateLevels,"KBO::levels");
  DEALLOC_UNKNOWN(_predicatePrecedences,"KBO::predPrecedences");
  if(_functions) {
    DEALLOC_UNKNOWN(_functionPrecedences,"KBO::funPrecedences");
  }
//  DEALLOC_KNOWN(_predicateLevels,sizeof(int)*_predicates,"KBO::levels");
//  DEALLOC_KNOWN(_predicatePrecedences,sizeof(int)*_predicates,"KBO::predPrecedences");
//  if(_functions) {
//    DEALLOC_KNOWN(_functionPrecedences,sizeof(int)*_functions,"KBO::funPrecedences");
//  }
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

Ordering::Result KBO::compare(TermList* t1, TermList* t2)
{
  CALL("KBO::compare(TermList*)");

  ASSERTION_VIOLATION;

  return INCOMPARABLE;
}

KBO* KBO::createReversedAgePreferenceConstantLevels()
{
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

}
