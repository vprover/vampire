/**
 * @file KBO.cpp
 * Implements class KBO for instances of the Knuth-Bendix ordering
 *
 * @since 30/04/2008 flight Brussels-Tel Aviv
 */

#include "../Debug/Tracer.hpp"

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
    : _result(EQUAL),
      _kbo(kbo)
  {}
  Result result();
  void traverse(const Literal* lit,int coefficient);
  Result compareList(const TermList*,const TermList*,
		     bool update,int priorityDiff);
private:
  class Var;
  /** First comparison result */
  Result _result;
  /** The ordering used */
  KBO& _kbo;
  /** The variable counters */
}; // class KBO::State 

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
    Result result = state.compareList(l1->args(),l2->args(),true,0);
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
  state.traverse(l1,1);
  state.traverse(l2,-1);
  Result res = state.result();
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
