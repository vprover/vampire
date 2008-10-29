/**
 * @file Tautology.cpp
 * Implements class Tautology implementing tautology-checking.
 * @since 05/01/2008 Torrevieja
 */

#include "../Lib/DArray.hpp"
#include "../Lib/Random.hpp"
#include "../Lib/Environment.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"

#include "../Shell/Statistics.hpp"

#include "Tautology.hpp"

using namespace Resolution;

/**
 * If @b c is a tautology, return true and update the statistics.
 * Otherwise, return false.
 * @since 05/01/2008 Torrevieja
 */

bool Tautology::isTautology(Clause* c)
{
  CALL("Tautology::isTautology");

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
    if (l->isEquality()) {
      TermList* t1 = l->args();
      TermList* t2 = t1->next();
      if (t1->sameContent(t2)) { // literal t = t
	env.statistics->equationalTautologies++;
 	return true;
      }
    }
    plits[pos++] = l;
  }
  if (pos == 0 || neg == 0) {
    return false;
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
	  return false;
	}
	break;
      case 0:
	env.statistics->simpleTautologies++;
	return true;
      case 1:
	n++;
	if (n >= neg) {
	  return false;
	}
	break;
      }
  }
} // Tautology::isTautology

/**
 * Compare two literals using the following order:
 * <ol>
 *  <li>First, using their predicate symbol numbers.</li>
 *  <li>Second, using their arguments (as void pointers).</li>
 * </ol>
 * @since 05/01/2008 Torrevieja
 */
int Tautology::compare(Literal* l1,Literal* l2)
{
  CALL("Tautology::compare");

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
    unsigned c1 = ts1->content();
    unsigned c2 = ts2->content();
    if (c1 < c2) {
      return -1;
    }
    if (c1 > c2) {
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
void Tautology::sort(Literal** lits,int to)
{
  CALL("Tautology::sort");
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
