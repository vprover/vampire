/**
 * @file Unprocessed.cpp
 * Implements class Unprocessed for the queue of unprocessed clauses.
 * @since 30/12/2007 Manchester
 */

#include "../Lib/Environment.hpp"

#include "../Kernel/Term.hpp"
#include "../Kernel/Clause.hpp"

#include "../Shell/Statistics.hpp"

#include "Unprocessed.hpp"

using namespace Kernel;
using namespace Resolution;

/**
 * Comparison of clause. The comparison uses four orders in the
 * following order:
 * <ol><li>by weight;</li>
 *     <li>by age;</li>
 *     <li>by input type;</li>
 *     <li>by number.</li>
 * </ol>
 * @since 30/12/2007 Manchester
 */
bool Unprocessed::lessThan(const Clause* c1,const Clause* c2)
{
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
} // lessThan


/**
 * Process the clause and inserts it to the queue. The processing includes
 * computing the weight and changing the storage class.
 * @since 30/12/2007 Manchester
 */
void Unprocessed::add(Clause& c)
{
  if (! c.weight()) {
    c.computeWeight();
  }
  c.setStore(Clause::UNPROCESSED);
  insert(&c);

  env.statistics->generatedClauses++;
} // Unprocessed::add
