/**
 * @file Resolution/ProofAttempt.cpp
 * Implements class ProofAttempt of resolution proof attempts.
 * @since 30/12/2007 Manchester
 */

#include "../Lib/Environment.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/Random.hpp"

#include "../Kernel/Clause.hpp"
#include "../Kernel/Term.hpp"
#include "../Kernel/Inference.hpp"

#include "../Shell/Statistics.hpp"
#include "../Shell/Options.hpp"

#include "LiteralSelection.hpp"
#include "Tautology.hpp"
#include "BinaryResolution.hpp"
#include "ProofAttempt.hpp"

using namespace Shell;
using namespace Resolution;

/**
 * Add an initial (input) clause c. Its age is set to 0 and it is added
 * to the queue of unprocessed clauses.
 * @since 30/12/2007 Manchester
 */
void ProofAttempt::initialClause(Clause* c)
{
  CALL("ProofAttempt::initialClause");

  c->setAge(0);
  _unprocessed.add(*c);
  env.statistics->initialClauses++;
}

/**
 * Saturate using the current options starting with the
 * current set of unprocessed clauses.
 */
void ProofAttempt::saturate()
{
  CALL("ProofAttempt::saturate");

  _passive.setAgeWeightRatio(env.options->ageRatio(),
			     env.options->weightRatio());

  for (;;) {
    while (! _unprocessed.isEmpty()) {
      Clause* c = _unprocessed.pop();
      Clause* pc = processUnprocessed(c);
      if (! pc) { // not retained
	continue;
      }
      if (env.options->showPassive()) {
	env.out << '*' << pc->toString() << "\n";
      }
      addToPassive(pc);
      if (pc->isEmpty()) {
	// proof found
	env.statistics->terminationReason = Statistics::REFUTATION;
	env.statistics->refutation = pc;
	return;
      }
    }
    if (env.timeLimitReached()) {
      return;
    }
    if (_passive.isEmpty()) {
      env.statistics->terminationReason = Statistics::UNKNOWN;
      return;
    }
    Clause* c = _passive.select();
    Clause* pc = processPassive(c);
    if (! pc) {
      continue;
    }
    if (pc->isEmpty()) {
      // proof found
      env.statistics->terminationReason = Statistics::REFUTATION;
      env.statistics->refutation = pc;
      return;
    }
    _active.insert(pc);
    if (env.options->showActive()) {
      env.out << pc->toString() << "\n";
    }
    if (env.timeLimitReached()) {
      return;
    }
    generatingInferences(pc);
  }
} // ProofAttempt::saturate


/**
 * Add clause @b c to the set of passive clauses.
 * No processing is made.
 */
void ProofAttempt::addToPassive(Clause* c)
{
  CALL("ProofAttempt::addToPassive");

  _passive.add(*c);
} 

/**
 * Processing an unprocessed clause consists of 
 * <ol>
 *  <li>Removing duplicate literals;</li>
 *  <li>Removing trivial inequalities <i>s != s</i>;</li>
 *  <li>Tautology checking.</li>
 * </ol>
 * If the clause is eliminated during processing, the function returns 0.
 * Otherwise, it returns the processed clause (which might be @b c itself).
 */
Clause* ProofAttempt::processUnprocessed(Clause* c)
{
  CALL("ProofAttempt::processUnprocessed");

  c = removeTrivialInequalities(c);
  c = removeDuplicateLiterals(c);
  if (Tautology::isTautology(c)) {
    return 0;
  }
  return c;
} // ProofAttempt::processUnprocessed

/**
 * Check if @b c has duplicate literals. If it does, they are
 * removed and a new clause is created and returned. Otherwise,
 * returns @b c. 
 * Implemented as a randomised quicksort algorithm.
 * @since 02/01/2008 Manchester
 */
Clause* ProofAttempt::removeDuplicateLiterals(Clause* c)
{
  CALL("ProofAttempt::removeDuplicateLiterals");

  int length = c->length();
  if (length <= 1) {
    return c;
  }

  // array behaves as a stack of calls to quicksort
  static DArray<int> ft(32);
  static DArray<Literal*> lits(32); // literals to sort
  ft.ensure(length);
  lits.ensure(length);

  int p = 0; // pointer to the next element in ft
  for (int i = length-1;i >= 0;i--) {
    lits[i] = (*c)[i];
  }

  // sorting will be between from and to
  int from = 0;
  int to = length-1;
  int found = 0;
  for (;;) {
    // invariant: from < to
    int m = from + Random::getInteger(to-from+1);
    Literal* mid = lits[m];
    int l = from;
    int r = to;
    while (l < m) {
      if ((void*)lits[l] < (void*)mid) {
	l++;
      }
      else if ((void*)lits[l] == (void*)mid) {
	found++;
	lits[l] = lits[from];
	lits[from] = 0;
	from++;
	l++;
      }
      else if (m == r) {
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
    }
    // l == m
    // now literals in lits[from ... m-1] are smaller than lits[m]
    // and literals in lits[r+1 ... to] are greater than lits[m]
    while (m < r) {
      if ((void*)mid < (void*)lits[m+1]) {
	Literal* lit = lits[r];
	lits[r] = lits[m+1];
	lits[m+1] = lit;
	r--;
      }
      else if ((void*)mid == (void*)lits[m+1]) {
	found++;
	lits[m+1] = lits[r];
	lits[r] = lits[to];
	lits[to] = 0;
	to--;
	r--;
      }
      else {
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

    // the stack is empty, finished
    if (found == 0) {
      return c;
    }
    // there are duplicate literals, delete them from lits
    int newLength = length - found;
    // now lits[0 ... newLength-1] contain the remaining literals
    env.statistics->duplicateLiterals += found;
    Clause* d = new(newLength)
                   Clause(newLength,
			  c->inputType(),
			  new Inference1(Inference::REMOVE_DUPLICATE_LITERALS,
					 c));
    int next = 0;
    for (int f = length-1;f >= 0;f--) {
      if (lits[f]) {
	(*d)[next++] = lits[f];
      }
    }
    ASS(next == newLength);
    d->setAge(c->age());
    d->computeWeight();
    d->setStore(Clause::UNPROCESSED);

    return d;
  }
} // ProofAttempt::removeDuplicateLiterals

/**
 * Check if @b c has literals <i>s != s</i>. If it does, they are
 * removed and a new clause is created and returned. Otherwise,
 * returns @b c. Implemented similar to the randomised quicksort.
 * @since 02/01/2008 Manchester
 */
Clause* ProofAttempt::removeTrivialInequalities(Clause* c)
{
  CALL("ProofAttempt::removeTrivialInequalities");

  static DArray<Literal*> lits(32);

  int length = c->length();
  int j = 0;
  lits.ensure(length);
  int found = 0;
  for (int i = length-1;i >= 0;i--) {
    Literal* l = (*c)[i];
    if (l->isPositive() || ! l->isEquality()) {
      lits[j++] = l;
      continue;
    }
    TermList* t1 = l->args();
    TermList* t2 = t1->next();
    if (t1->sameContent(t2)) {
      found++;
    }
    else {
      lits[j++] = l;
    }
  }

  if (found == 0) {
    return c;
  }

  env.statistics->trivialInequalities += found;
  int newLength = length - found;
  Clause* d = new(newLength)
                Clause(newLength,
		       c->inputType(),
		       new Inference1(Inference::TRIVIAL_INEQUALITY_REMOVAL,
				      c));
  for (int i = newLength-1;i >= 0;i--) {
    (*d)[i] = lits[newLength-i-1];
  }
  d->setAge(c->age());
  d->computeWeight();
  d->setStore(Clause::UNPROCESSED);

  return d;
} // removeTrivialInequalities


/**
 * Processing a passive clause consists of 
 * <ol>
 *  <li>Literal selection.</li>
 * </ol>
 */
Clause* ProofAttempt::processPassive(Clause* c)
{
  CALL("ProofAttempt::processPassive");

  LiteralSelection::select(c);
  return c;
} // ProofAttempt::processUnprocessed

void ProofAttempt::generatingInferences(Clause* c)
{
  CALL("ProofAttempt::generatingInferences");

  BinaryResolution res(*c,*this);
  res.apply();
} // ProofAttempt::generatingInferences
