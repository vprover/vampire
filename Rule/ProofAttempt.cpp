/**
 * @file Rule/ProofAttempt.cpp
 * Implements class ProofAttempt of rule-based proof attempts.
 * @since 12/07/2008 Linz
 */

#include "../Debug/Tracer.hpp"
#include "../Lib/Environment.hpp"
#include "../Shell/Statistics.hpp"

#include "ProofAttempt.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Rule;

/**
 * Add an initial (input) clause c. Its age is set to 0 and it is added
 * to the queue of unprocessed clauses.
 * @since 30/12/2007 Manchester
 */
// void ProofAttempt::initialClause(Clause* c)
// {
//   CALL("ProofAttempt::initialClause");

//   env.statistics->initialClauses++;
// }

/**
 * Saturate using the current options starting with the
 * current set of unprocessed clauses.
 */
void ProofAttempt::prove(UnitList* units)
{
  CALL("ProofAttempt::prove");

} // ProofAttempt::prove

