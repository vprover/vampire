/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "../Debug/Tracer.hpp"
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
    : weightDiff(0), negNum(0), posNum(0),
      _lexResult(EQUAL),
      _kbo(kbo)
  {}
  Result innerResult(TermList tl1, TermList tl2);
  void traverse(TermList tl,int coefficient);
  Result compare(const Literal* l1, const Literal* l2);
private:
  void recordVariable(unsigned var, int coef);

  int weightDiff;
  DHMap<unsigned, int, IdHash> varDiffs;
  int negNum;
  int posNum;
  /** First comparison result */
  Result _lexResult;
  /** The ordering used */
  KBO& _kbo;
  /** The variable counters */
}; // class KBO::State

Ordering::Result KBO::State::innerResult(TermList tl1, TermList tl2)
{
  CALL("KBO::State::innerResult");
  ASS(!tl1.sameContent(*tl2));
  ASS(!TermList::sameTopFunctor(&tl1,&tl2));
  if(posNum==0 && negNum==0) {
    //all variables occur the same number of times in tl1 and tl2
    if(weightDiff) {
      return weightDiff>0 ? GREATER : LESS;
    } else {
      //if tl1 or tl2 is a variable, the same variable must occur
      //also in the other term, but not in top level, as they would
      //have same content
      if(tl1.isVar()) {
	return LESS;
      } else if(tl2.isVar()) {
	return GREATER;
      } else {
	int prec1=_kbo.functionPrecedence(tl1.term()->functor());
	int prec2=_kbo.functionPrecedence(tl2.term()->functor());
	if(prec1>prec2) {
	  return GREATER;
	} else {
	  ASS(prec1!=prec2);//precedence ordering must be total
	  return LESS;
	}
      }
    }
  } else if(posNum==0) {
    //TODO
  } else if(negNum==0) {
    //TODO
  } else {
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
      posNum--;
    } else if(*pnum==-1) {
      negNum++;
    }
  } else {
    if(*pnum==0) {
      negNum--;
    } else if(*pnum==1) {
      posNum++;
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

  weightDiff+=_kbo.functionSymbolWeight(tl.term()->functor())*coef;

  TermList* ts=tl.term()->args();
  static Stack<TermList*> stack(4);
  for(;;) {
    if(!ts->next()->isEmpty()) {
      stack.push(ts->next());
    }
    if(ts->isTerm()) {
      stack.push(ts->term()->args());
      weightDiff+=_kbo.functionSymbolWeight(ts->term()->functor())*coef;
    } else {
      ASS(ts->isOrdinaryVar());
      weightDiff+=_kbo._variableWeight*coef;
      recordVariable(ts->var(), coef);
    }
    if(stack.isEmpty()) {
      break;
    }
    ts=stack.pop();
  }
}

Ordering::Result KBO::State::compare(const Literal* l1, const Literal* l2)
{
  CALL("KBO::State::compare");

  weightDiff+=_kbo.predicateHeaderWeight(l1->header());
  weightDiff-=_kbo.predicateHeaderWeight(l2->header());

  const TermList* ss=l1->args();
  const TermList* tt=l2->args();
  static Stack<const TermList*> stack(4);
  for(;;) {
    if(!ss->next()->isEmpty()) {
      ASS(!tt->next()->isEmpty());
      stack.push(ss->next());
      stack.push(tt->next());
    }
    //if content is the same, neighter weightDiff nor varDiffs change
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
  CALL("KBO::KBOW");

  _predicateLevels = (int*)ALLOC_UNKNOWN(sizeof(int)*_predicates,
					 "KBO::levels");
  _predicatePrecedences = (int*)ALLOC_UNKNOWN(sizeof(int)*_predicates,
					      "KBO::predPrecedences");
  _functionPrecedences = (int*)ALLOC_UNKNOWN(sizeof(int)*_functions,
					     "KBO::funPrecedences");
} // KBO::KBO

KBO::~KBO()
{
  CALL("KBO::~KBO");

  DEALLOC_UNKNOWN(_predicateLevels,"KBO::levels");
  DEALLOC_UNKNOWN(_predicatePrecedences,"KBO::predPrecedences");
  DEALLOC_UNKNOWN(_functionPrecedences,"KBO::funPrecedences");
} // KBO::~KBO

/**
 * Compare arguments of literals l1 and l2 and return the result
 * of the comparison.
 * @since 07/05/2008 flight Manchester-Brussels
 */
Ordering::Result KBO::compare(const Literal* l1,const Literal* l2)
{
  CALL("KBO::compare(Literal*)");
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

  // now predicate levels of l1 and l2 are the same
  State state(*this);
  if (p1 == p2) {
    Result result ;//= state.compareList(l1->args(),l2->args(),true,0);
    switch (result) {
    case GREATER:
    case LESS:
    case INCOMPARABLE:
      return result;

    case GREATER_EQ:
      if (l1->isPositive()) {
	if(l2->isPositive()) {
	  return GREATER_EQ;
	}
	return INCOMPARABLE;
      }
      // l1 is negative
      if(l2->isNegative()) {
	return GREATER_EQ;
      }
      return GREATER;

    case LESS_EQ:
      if (l2->isPositive()) {
	if(l1->isPositive()) {
	  return LESS_EQ;
	}
	return INCOMPARABLE;
      }
      // l2 is negative
      if(l1->isNegative()) {
	return LESS_EQ;
      }
      return GREATER;

    case EQUAL:
      if (l1->isPositive()) {
	ASS(l2->isNegative());
	return LESS;
      }
      ASS(l2->isPositive());
      return GREATER;
    }
  }

//   if (l1->commutative() && l1->functor() == l2->functor()) {
//     l1->orderArguments(*this);
//     l2->orderArguments(*this);
//   }

  // p1 != p2

  Result res = state.compare(l1,l2);
  switch (res) {
  case GREATER:
  case LESS:
  case INCOMPARABLE:
    return res;

  case GREATER_EQ:
    return predicatePrecedence(p1) > predicatePrecedence(p2)
           ? GREATER
           : INCOMPARABLE;
  case LESS_EQ:
    return predicatePrecedence(p1) < predicatePrecedence(p2)
           ? LESS
           : INCOMPARABLE;
  case EQUAL:
    return predicatePrecedence(p1) < predicatePrecedence(p2)
           ? LESS
           : GREATER;
  }
#if VDEBUG
  ASS(false);
#endif
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
 * @b _predicates, then the value is taken from the array _predicateLevels,
 * otherwise it is defined to be 1 (to make it greater than the level
 * of equality).
 * @since 11/05/2008 Manchester
 */
int KBO::predicatePrecedence (unsigned pred)
{
  return pred > _predicates ? 1 : _predicatePrecedences[pred];
} // KBO::predicatePrecedences


Ordering::Result KBO::compare(const TermList* t1,const TermList* t2)
{
  CALL("KBO::compare(TermList*)");

  return INCOMPARABLE;
}

}
