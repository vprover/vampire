/**
 * @file Statistics.cpp
 * Implements proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#include <iostream>

#include "../Lib/Environment.hpp"
#include "Statistics.hpp"

using namespace std;
using namespace Lib;
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
    forwardSuperposition(0),
    backwardSuperposition(0),
    equalityFactoring(0),
    equalityResolution(0),
    duplicateLiterals(0),
    trivialInequalities(0),
    simpleTautologies(0),
    equationalTautologies(0),
    forwardSubsumed(0),
    backwardSubsumed(0),
    forwardSubsumptionResolution(0),
    generatedClauses(0),
    passiveClauses(0),
    activeClauses(0),
    terminationReason(UNKNOWN),
    refutation(0)
{
} // Statistics::Statistics


void Statistics::print()
{
  env.out << "------------------------------\n";
  env.out << "Active clauses: "<<activeClauses<<endl;
  env.out << "Passive clauses: "<<passiveClauses<<endl;
  env.out << "Generated clauses: "<<generatedClauses<<endl;
  env.out << endl;

  env.out << "Duplicate literals: "<<duplicateLiterals<<endl;
  env.out << "Trivial inequalities: "<<trivialInequalities<<endl;
  env.out << "Simple tautologies: "<<simpleTautologies<<endl;
  env.out << "Equational tautologies: "<<equationalTautologies<<endl;
  env.out << "Forward subsumptions: "<<forwardSubsumed<<endl;
  env.out << "Backward subsumptions: "<<backwardSubsumed<<endl;
  env.out << "Fw subsumption resolutions: "<<forwardSubsumptionResolution<<endl;
  env.out << endl;

  env.out << "Binary resolution: "<<resolution<<endl;
  env.out << "Factoring: "<<factoring<<endl;
  env.out << "Forward superposition: "<<forwardSuperposition<<endl;
  env.out << "Backward superposition: "<<backwardSuperposition<<endl;
  env.out << "Equality factoring: "<<equalityFactoring<<endl;
  env.out << "Equality resolution: "<<equalityResolution<<endl;
  env.out << "------------------------------\n";
}
