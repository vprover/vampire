/**
 * @file Statistics.cpp
 * Implements proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#include "Statistics.hpp"

using namespace Shell;

/**
 * Iniitalise statistics.
 * @since 02/01/2008 Manchester
 */
Statistics::Statistics()
  : inputClauses(0),
    inputFormulas(0),
    formulaNames(0),
    initialClauses(0),
    factoring(0),
    resolution(0),
    duplicateLiterals(0),
    trivialInequalities(0),
    simpleTautologies(0),
    equationalTautologies(0),
    forwardSubsumed(0),
    generatedClauses(0),
    passiveClauses(0),
    activeClauses(0),
    terminationReason(UNKNOWN),
    refutation(0)
{
} // Statistics::Statistics

