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
 * @file TautologyDeletionISE.cpp
 * Implements class TautologyDeletionISE.
 */

#include "Lib/Random.hpp"
#include "Lib/Environment.hpp"
#include "Lib/DArray.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Shell/Statistics.hpp"
#include "TautologyDeletionISE.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Inferences;


Clause* TautologyDeletionISE::simplify(Clause* c)
{
  CALL("TautologyDeletionISE::simplify");

  static DArray<Literal*> plits(32); // array of positive literals
  static DArray<Literal*> nlits(32); // array of negative literals

  int pos = 0;
  int neg = 0;
  int length = c->length();
  plits.ensure(length);
  nlits.ensure(length);
  for (int i = length-1; i >= 0;i--) {
    Literal* l = (*c)[i];
    if (l->isNegative()) {
      nlits[neg++] = l;
      continue;
    }
    // l is positive
    if (_deleteEqTautologies && EqHelper::isEqTautology(l)) {
      // literal t = t
      env.statistics->equationalTautologies++;
      return 0;
    }
    plits[pos++] = l;
  }
  if (pos == 0 || neg == 0) {
    return c;
  }
  if (pos > 1) {
    sort(plits.array(),pos);
  }
  if (neg > 1) {
    sort(nlits.array(),neg);
  }
  int p = 0;
  int n = 0;
  for (;;) {
    switch (compare(plits[p],nlits[n]))
      {
      case -1:
        p++;
        if (p >= pos) {
          return c;
        }
        break;
      case 0:
        env.statistics->simpleTautologies++;
        return 0;
      case 1:
        n++;
        if (n >= neg) {
          return c;
        }
        break;
      }
  }
}

/**
 * Compare two literals using the following order:
 * <ol>
 *  <li>First, using their predicate symbol numbers.</li>
 *  <li>Second, using their arguments (as void pointers).</li>
 * </ol>
 * @since 05/01/2008 Torrevieja
 */
int TautologyDeletionISE::compare(Literal* l1,Literal* l2)
{
  CALL("TautologyDeletionISE::compare");

  unsigned f1 = l1->functor();
  unsigned f2 = l2->functor();
  if (f1 < f2) {
    return -1;
  }
  if (f1 > f2) {
    return 1;
  }
  TermList* ts1 = l1->args();
  TermList* ts2 = l2->args();
  while (! ts1->isEmpty()) {
    unsigned varOrId1;
    unsigned varOrId2;

    if (ts1->isVar()) {
      if (ts2->isVar()) { // both variables, let's compare them
        varOrId1 = ts1->var();
        varOrId2 = ts2->var();
      } else {
        return -1;
      }
    } else {
      if (ts2->isVar()) {
        return 1;
      } else { // neither is var, let's compare the ids
        varOrId1 = ts1->term()->getId();
        varOrId2 = ts2->term()->getId();
      }
    }

    if (varOrId1 < varOrId2) {
      return -1;
    }
    if (varOrId1 > varOrId2) {
      return 1;
    }
    ts1 = ts1->next();
    ts2 = ts2->next();
  }
  return 0;
} // Tautology::compare

/**
 * Randomised quicksort of an array @b lits of literals between
 *  indexes 0 and to-1 using compare()
 * @pre the array has no duplicate literals, that is, compare()
 *    never returns 0
 * @since 05/01/2008 Torrevieja
 */
void TautologyDeletionISE::sort(Literal** lits,int to)
{
  CALL("TautologyDeletionISE::sort");
  ASS(to > 1);

  // array behaves as a stack of calls to quicksort
  static DArray<int> ft(32);

  to--;
  ft.ensure(to);
  int from = 0;

  int p = 0; // pointer to the next element in ft
  for (;;) {
    // invariant: from < to
    int m = from + Random::getInteger(to-from+1);
    Literal* mid = lits[m];
    int l = from;
    int r = to;
    while (l < m) {
      switch (compare(lits[l],mid))
	{
	case -1:
	  l++;
	  break;
#if VDEBUG
	case 0:
	  ASSERTION_VIOLATION;
#endif
	case 1:
	  if (m == r) {
	    lits[m] = lits[l];
	    lits[l] = lits[m-1];
	    lits[m-1] = mid;
	    m--;
	    r--;
	  }
	  else {
	    ASS(m < r);
	    Literal* lit = lits[l];
	    lits[l] = lits[r];
	    lits[r] = lit;
	    r--;
	  }
	  break;
	}
    }
    // l == m
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and literals in lits[r+1 ... to] are greater than lits[m]
    while (m < r) {
      switch (compare(mid,lits[m+1]))
	{
	case -1:
	  {
	    Literal* lit = lits[r];
	    lits[r] = lits[m+1];
	    lits[m+1] = lit;
	    r--;
	  }
	  break;
#if VDEBUG
	case 0:
	  ASSERTION_VIOLATION;
#endif
	case 1:
	  lits[m] = lits[m+1];
	  lits[m+1] = mid;
	  m++;
	}
    }
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and all literals in lits[m+1 ... to] are greater than lits[m]
    if (m+1 < to) {
      ft[p++] = m+1;
      ft[p++] = to;
    }

    to = m-1;
    if (from < to) {
      continue;
    }
    if (p != 0) {
      p -= 2;
      ASS(p >= 0);
      from = ft[p];
      to = ft[p+1];
      continue;
    }
    return;
  }
} // Tautology::sort

