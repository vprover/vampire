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
 * @file LPO.cpp
 * Implements class LPO for instances of the lexicographic path
 * ordering based on Bernd Loechner's thesis "Advances in
 * Equational Theorem Proving - Architecture, Algorithms, and
 * Redundancy Avoidance" Section 4.2
 */

#include "Debug/Tracer.hpp"


#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"

#include "Shell/Options.hpp"

#include "Term.hpp"
#include "LPO.hpp"
#include "Signature.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;

/**
 * Compare arguments of non-equality literals l1 and l2 and return the
 * result of the comparison.
 */
Ordering::Result LPO::comparePredicates(Literal* l1, Literal *l2) const
{
  CALL("LPO::comparePredicates");
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if (p1 == p2) {
    ASS_EQ(l1->isNegative(), l1->isNegative()) // this assertion is meaningless. 
    //maybe:  ASS_EQ(l1->isNegative(), l2->isNegative())

    // compare arguments in lexicographic order
    for (unsigned i = 0; i < l1->arity(); i++) {
      Result res = compare(*l1->nthArgument(i), *l2->nthArgument(i));
      if (res != EQUAL)
        return res;
    }
    return EQUAL;
  }

  ASS_NEQ(predicatePrecedence(p1), predicatePrecedence(p2)); // precedence should be total
  return (predicatePrecedence(p1) > predicatePrecedence(p2)) ? GREATER : LESS;
} // LPO::comparePredicates()

Ordering::Result LPO::compare(TermList tl1, TermList tl2) const
{
  CALL("LPO::compare(TermList, TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
  }
  ASS(tl1.isTerm());
  return clpo(tl1.term(), tl2);
}

Ordering::Result LPO::clpo(Term* t1, TermList tl2) const
{
  CALL("LPO::clpo");
  ASS(t1->shared());

  if(tl2.isOrdinaryVar()) {
    return t1->containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }
  
  ASS(tl2.isTerm());
  Term* t2=tl2.term();

  switch (compareFunctionPrecedences(t1->functor(), t2->functor())) {
  case EQUAL:
    return cLMA(t1, t2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return cMA(t1, t2->args(), t2->arity());
  case LESS:
    return Ordering::reverse(cMA(t2, t1->args(), t1->arity()));
  default:
    ASSERTION_VIOLATION;
    // shouldn't happen because symbol precedence is assumed to be
    // total, but if it is not then the following call is correct
    //
    // return cAA(t1, t2, t1->args(), t2->args(), t1->arity(), t2->arity());
  }
}

/*
 * All TermList* are stored in reverse order (by design in Term),
 * hence the weird pointer arithmetic
 */
Ordering::Result LPO::cMA(Term *s, TermList* tl, unsigned arity) const
{
  CALL("LPO::cMA");

  ASS(s->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch(clpo(s, *(tl - i))) {
    case EQUAL:
    case LESS:
      return LESS;
    case INCOMPARABLE:
      return reverse(alpha(tl - i - 1, arity - i - 1, s));
    case GREATER:
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return GREATER;
}

Ordering::Result LPO::cLMA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const
{
  CALL("LPO::cLMA");
  ASS(s->shared());
  ASS(t->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch(compare(*(sl - i), *(tl - i))) {
    case EQUAL:
      break;
    case GREATER:
      return cMA(s, tl - i - 1, arity - i - 1);
    case LESS:
      return reverse(cMA(t, sl - i - 1, arity - i - 1));
    case INCOMPARABLE:
      return cAA(s, t, sl - i - 1, tl - i - 1, arity - i - 1, arity - i - 1);
    default:
      ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

Ordering::Result LPO::cAA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity1, unsigned arity2) const
{
  CALL("LPO::cAA");
  ASS(s->shared());
  ASS(t->shared());

  switch (alpha(sl, arity1, t)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return reverse(alpha(tl, arity2, s));
  default:
    ASSERTION_VIOLATION;
  }
}

// greater iff some exists s_i in sl such that s_i >= t 
Ordering::Result LPO::alpha(TermList* sl, unsigned arity, Term *t) const
{
  CALL("LPO::alpha");
  ASS(t->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch (lpo(*(sl - i), TermList(t))) {
    case EQUAL:
    case GREATER:
      return GREATER;
    case LESS:
    case INCOMPARABLE:
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return INCOMPARABLE;
}

// unidirectional comparison function (returns correct result if tl1 >
// tl2 or tl1 = tl2)
Ordering::Result LPO::lpo(TermList tl1, TermList tl2) const
{
  CALL("LPO::lpo(TermList, TermList)");

  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    return INCOMPARABLE;
  }
  ASS(tl1.isTerm());
  Term* t1 = tl1.term();
  ASS(t1->shared());

  if(tl2.isOrdinaryVar()) {
    return t1->containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }

  ASS(tl2.isTerm());
  Term* t2=tl2.term();

  switch (compareFunctionPrecedences(t1->functor(), t2->functor())) {
  case EQUAL:
    return lexMAE(t1, t2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return majo(t1, t2->args(), t2->arity());
  default:
    return alpha(t1->args(), t1->arity(), t2);
  }
}

Ordering::Result LPO::lexMAE(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const
{
  CALL("LPO::lexMAE");

  ASS(s->shared());
  ASS(t->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch (lpo(*(sl - i), *(tl - i))) {
    case EQUAL:
      break;
    case GREATER:
      return majo(s, tl - i - 1, arity - i - 1);
    case INCOMPARABLE:
      return alpha(sl - i - 1, arity - i - 1, t);
    default:
      ASSERTION_VIOLATION;
    }
  }
  // reached only when the terms are equal but this is checked already
  // at the start of LPO::lpo, which is the only caller of this function
  ASSERTION_VIOLATION;
}

// greater if s is greater than every term in tl
Ordering::Result LPO::majo(Term* s, TermList* tl, unsigned arity) const
{
  CALL("LPO::majo");

  ASS(s->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch(lpo(TermList(s), *(tl - i))) {
    case GREATER:
      break;
    case EQUAL:
    case INCOMPARABLE:
      return INCOMPARABLE;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return GREATER;
}

void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
