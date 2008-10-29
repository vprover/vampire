/**
 * @file Active.cpp
 * Implements class Active for the queue of active clauses.
 * @since 04/01/2008 flight Manchester-Murcia
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"

#include "../Shell/Statistics.hpp"

#include "Active.hpp"

using namespace Kernel;
using namespace Resolution;

/**
 * Comparison of clauses. The comparison uses four orders in the
 * following order:
 * <ol><li>by weight;</li>
 *     <li>by age;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 04/01/2008 flight Manchester-Murcia
 */
bool Active::lessThan(const Clause* c1,const Clause* c2)
{
  CALL("WeightQueue::lessThan");

  if (c1->weight() < c2->weight()) {
    return true;
  }
  if (c2->weight() < c1->weight()) {
    return false;
  }
  if (c1->age() < c2->age()) {
    return true;
  }
  if (c2->age() < c1->age()) {
    return false;
  }
  if (c1->inputType() < c2->inputType()) {
    return false;
  }
  if (c2->inputType() < c1->inputType()) {
    return true;
  }
  return c1->number() < c2->number();
} // Active::lessThan


/**
 * Add @b c clause to the queue.
 * @since 04/01/2008 flight Manchester-Murcia
 */
void Active::add(Clause& c)
{
  CALL("Active::add");

  insert(&c);
  c.setStore(Clause::ACTIVE);
  env.statistics->activeClauses++;
} // Active::add

