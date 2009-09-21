/**
 * @file Statistics.cpp
 * Implements proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#include <iostream>

#include "../Lib/Allocator.hpp"
#include "../Lib/Environment.hpp"
#include "../Lib/Timer.hpp"
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
    splittedInequalities(0),
    purePredicates(0),
    unusedPredicateDefinitions(0),
    functionDefinitions(0),
    factoring(0),
    resolution(0),
    forwardSuperposition(0),
    backwardSuperposition(0),
    selfSuperposition(0),
    equalityFactoring(0),
    equalityResolution(0),
    duplicateLiterals(0),
    trivialInequalities(0),
    forwardSubsumptionResolution(0),
    forwardDemodulations(0),
    forwardDemodulationsToEqTaut(0),
    backwardDemodulations(0),
    backwardDemodulationsToEqTaut(0),
    condensations(0),
    evaluations(0),
    simpleTautologies(0),
    equationalTautologies(0),
    forwardSubsumed(0),
    backwardSubsumed(0),
    generatedClauses(0),
    passiveClauses(0),
    activeClauses(0),
    finalPassiveClauses(0),
    finalActiveClauses(0),
    splittedClauses(0),
    splittedComponents(0),
    uniqueComponents(0),
    terminationReason(UNKNOWN),
    refutation(0)
{
} // Statistics::Statistics


void Statistics::print()
{
  bool separable=false;
#define COND_OUT(text, num) if(num) { env.out<<(text)<<": "<<(num)<<endl; separable=true; }
#define SEPARATOR if(separable) { env.out<<endl; separable=false; }

  env.out << "------------------------------\n";
  COND_OUT("Active clauses", activeClauses);
  COND_OUT("Passive clauses", passiveClauses);
  COND_OUT("Generated clauses", generatedClauses);
  COND_OUT("Final active clauses", finalActiveClauses);
  COND_OUT("Final passive clauses", finalPassiveClauses);
  COND_OUT("Input clauses", inputClauses);
  COND_OUT("Input formulas", inputFormulas);
  COND_OUT("Initial clauses", initialClauses);
  SEPARATOR;

  COND_OUT("Pure predicates", purePredicates);
  COND_OUT("Unused predicate definitions", unusedPredicateDefinitions);
  COND_OUT("Function definitions", functionDefinitions);
  COND_OUT("Splitted inequalities", splittedInequalities);
  SEPARATOR;

  COND_OUT("Duplicate literals", duplicateLiterals);
  COND_OUT("Trivial inequalities", trivialInequalities);
  COND_OUT("Fw subsumption resolutions", forwardSubsumptionResolution);
  COND_OUT("Fw demodulations", forwardDemodulations);
  COND_OUT("Bw demodulations", backwardDemodulations);
  COND_OUT("Condensations", condensations);
  COND_OUT("Evaluations", evaluations);
  SEPARATOR;

  COND_OUT("Simple tautologies", simpleTautologies);
  COND_OUT("Equational tautologies", equationalTautologies);
  COND_OUT("Forward subsumptions", forwardSubsumed);
  COND_OUT("Backward subsumptions", backwardSubsumed);
  COND_OUT("Fw demodulations to eq. taut.", forwardDemodulationsToEqTaut);
  COND_OUT("Bw demodulations to eq. taut.", backwardDemodulationsToEqTaut);
  SEPARATOR;

  COND_OUT("Binary resolution", resolution);
  COND_OUT("Factoring", factoring);
  COND_OUT("Forward superposition", forwardSuperposition);
  COND_OUT("Backward superposition", backwardSuperposition);
  COND_OUT("Self superposition", selfSuperposition);
  COND_OUT("Equality factoring", equalityFactoring);
  COND_OUT("Equality resolution", equalityResolution);
  SEPARATOR;

  COND_OUT("Splitted clauses", splittedClauses);
  COND_OUT("Splitted components", splittedComponents);
  COND_OUT("Unique components", uniqueComponents);
  SEPARATOR;

  env.out << "Memory used: " << (Allocator::getUsedMemory()/1024) << "KB" << endl;
  env.out << "Time elapsed: " << Timer::msToSecondsString(env.timer->elapsedMilliseconds()) << endl;
  env.out << "------------------------------\n";

#undef SEPARATOR
#undef COND_OUT
}
