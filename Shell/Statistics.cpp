/**
 * @file Statistics.cpp
 * Implements proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#include <iostream>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Allocator.hpp"
#include "Lib/Environment.hpp"
#include "Lib/TimeCounter.hpp"
#include "Lib/Timer.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Options.hpp"

#include "Statistics.hpp"


using namespace std;
using namespace Lib;
using namespace Saturation;
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
    propagatedEqualities(0),
    removedSingletonVariables(0),
    purePredicates(0),
    trivialPredicates(0),
    hornReversedPredicates(0),
    eprPreservingSkolemizations(0),
    inlinedPredicateDefinitions(0),
    mergedPredicateDefinitions(0),
    unusedPredicateDefinitions(0),
    functionDefinitions(0),
    selectedBySine(0),
    sineIterations(0),
    factoring(0),
    resolution(0),
    urResolution(0),
    forwardSuperposition(0),
    backwardSuperposition(0),
    selfSuperposition(0),
    equalityFactoring(0),
    equalityResolution(0),
    duplicateLiterals(0),
    trivialInequalities(0),
    forwardSubsumptionResolution(0),
    backwardSubsumptionResolution(0),
    forwardDemodulations(0),
    forwardDemodulationsToEqTaut(0),
    backwardDemodulations(0),
    backwardDemodulationsToEqTaut(0),
    forwardLiteralRewrites(0),
    condensations(0),
    globalSubsumption(0),
    evaluations(0),
    interpretedSimplifications(0),
    simpleTautologies(0),
    equationalTautologies(0),
    forwardSubsumed(0),
    backwardSubsumed(0),
    subsumedEmptyClauses(0),
    emptyClauseSubsumptions(0),
    subsumedByMarking(0),
    generatedClauses(0),
    passiveClauses(0),
    activeClauses(0),
    discardedNonRedundantClauses(0),
    inferencesSkippedDueToColors(0),
    finalPassiveClauses(0),
    finalActiveClauses(0),
    reactivatedClauses(0),
    splitClauses(0),
    splitComponents(0),
    uniqueComponents(0),
    splittingNamesIntroduced(0),
    bddPropClauses(0),
    satClauses(0),
    unitSatClauses(0),
    binarySatClauses(0),
    learntSatClauses(0),
    learntSatLiterals(0),
    bddMemoryUsage(0),

    backtrackingSplits(0),
    backtrackingSplitsRefuted(0),
    backtrackingSplitsRefutedZeroLevel(0),
    satSplits(0),
    satSplitRefutations(0),

    instGenGeneratedClauses(0),
    instGenRedundantClauses(0),
    instGenKeptClauses(0),
    instGenIterations(0),

    maxBFNTModelSize(0),

    satPureVarsEliminated(0),
    terminationReason(UNKNOWN),
    refutation(0),
    phase(INITIALIZATION)
{
} // Statistics::Statistics


void Statistics::print(ostream& out)
{
  if(env.options->statistics()==Options::STATISTICS_NONE) {
    return;
  }

  SaturationAlgorithm::tryUpdateFinalClauseCount();

  bool separable=false;
#define COND_OUT(text, num) if(num) { out<<(text)<<": "<<(num)<<endl; separable=true; }
#define SEPARATOR if(separable) { out<<endl; separable=false; }

  out << "------------------------------\n";
  out << "Version: " << VERSION_STRING << endl;

  out << "Termination reason: ";
  switch(terminationReason) {
  case Statistics::REFUTATION:
    out << "Refutation";
    break;
  case Statistics::TIME_LIMIT:
    out << "Time limit";
    break;
  case Statistics::MEMORY_LIMIT:
    out << "Memory limit";
    break;
  case Statistics::REFUTATION_NOT_FOUND:
    if(env.statistics->discardedNonRedundantClauses) {
      out << "Refutation not found, non-redundant clauses discarded";
    } else {
      out << "Refutation not found, incomplete strategy";
    }
    break;
  case Statistics::SATISFIABLE:
    out << "Satisfiable";
    break;
  case Statistics::UNKNOWN:
    out << "Unknown";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  out << endl;
  if(phase!=FINALIZATION) {
    out << "Termination phase: " << phaseToString(phase) << endl;
  }
  out << endl;

  COND_OUT("Active clauses", activeClauses);
  COND_OUT("Passive clauses", passiveClauses);
  COND_OUT("Generated clauses", generatedClauses);
  COND_OUT("Final active clauses", finalActiveClauses);
  COND_OUT("Final passive clauses", finalPassiveClauses);
  COND_OUT("Input clauses", inputClauses);
  COND_OUT("Input formulas", inputFormulas);
  COND_OUT("Initial clauses", initialClauses);
  COND_OUT("Discarded non-redundant clauses", discardedNonRedundantClauses);
  COND_OUT("Inferences skipped due to colors", inferencesSkippedDueToColors);
  COND_OUT("Reactivated clauses", reactivatedClauses);
  SEPARATOR;

  COND_OUT("Pure predicates", purePredicates);
  COND_OUT("Removed due to trivial predicates", trivialPredicates);
  COND_OUT("Predicates reversed for Horn", hornReversedPredicates);
  COND_OUT("EPR preserving skolemizations", eprPreservingSkolemizations);
  COND_OUT("Inlined predicate definitions", inlinedPredicateDefinitions);
  COND_OUT("Merged predicate definitions", mergedPredicateDefinitions);
  COND_OUT("Unused predicate definitions", unusedPredicateDefinitions);
  COND_OUT("Function definitions", functionDefinitions);
  COND_OUT("Selected by SInE selection", selectedBySine);
  COND_OUT("SInE iterations", sineIterations);
  COND_OUT("Splitted inequalities", splittedInequalities);
  COND_OUT("Propagated equalities", propagatedEqualities);
  COND_OUT("Removed singleton variables", removedSingletonVariables);
  SEPARATOR;

  COND_OUT("Duplicate literals", duplicateLiterals);
  COND_OUT("Trivial inequalities", trivialInequalities);
  COND_OUT("Fw subsumption resolutions", forwardSubsumptionResolution);
  COND_OUT("Bw subsumption resolutions", backwardSubsumptionResolution);
  COND_OUT("Fw demodulations", forwardDemodulations);
  COND_OUT("Bw demodulations", backwardDemodulations);
  COND_OUT("Fw literal rewrites", forwardLiteralRewrites);
  COND_OUT("Condensations", condensations);
  COND_OUT("Global subsumptions", globalSubsumption);
  COND_OUT("Evaluations", evaluations);
  COND_OUT("Interpreted simplifications", interpretedSimplifications);
  SEPARATOR;

  COND_OUT("Simple tautologies", simpleTautologies);
  COND_OUT("Equational tautologies", equationalTautologies);
  COND_OUT("Forward subsumptions", forwardSubsumed);
  COND_OUT("Backward subsumptions", backwardSubsumed);
  COND_OUT("Fw demodulations to eq. taut.", forwardDemodulationsToEqTaut);
  COND_OUT("Bw demodulations to eq. taut.", backwardDemodulationsToEqTaut);
  COND_OUT("Subsumed empty clauses", subsumedEmptyClauses);
  COND_OUT("Empty clause subsumptions", emptyClauseSubsumptions);
  COND_OUT("Subsumed by BDD marking", subsumedByMarking);
  SEPARATOR;

  COND_OUT("Binary resolution", resolution);
  COND_OUT("Unit resulting resolution", urResolution);
  COND_OUT("Factoring", factoring);
  COND_OUT("Forward superposition", forwardSuperposition);
  COND_OUT("Backward superposition", backwardSuperposition);
  COND_OUT("Self superposition", selfSuperposition);
  COND_OUT("Equality factoring", equalityFactoring);
  COND_OUT("Equality resolution", equalityResolution);
  SEPARATOR;

  COND_OUT("Split clauses", splitClauses);
  COND_OUT("Split components", splitComponents);
  COND_OUT("Unique components", uniqueComponents);
  COND_OUT("Introduced splitting names", splittingNamesIntroduced);
  COND_OUT("BDD propositional clauses", bddPropClauses);
  COND_OUT("SAT solver clauses", satClauses);
  COND_OUT("SAT solver unit clauses", unitSatClauses);
  COND_OUT("SAT solver binary clauses", binarySatClauses);
  COND_OUT("SAT solver learnt clauses", learntSatClauses);
  COND_OUT("SAT solver learnt literals", learntSatLiterals);
  COND_OUT("Memory used by BDDs [KB]", bddMemoryUsage/1024);
  SEPARATOR;

  COND_OUT("Backtracking splits", backtrackingSplits);
  COND_OUT("Backtracking splits refuted", backtrackingSplitsRefuted);
  COND_OUT("Backtracking splits refuted at zero level", backtrackingSplitsRefutedZeroLevel);
  COND_OUT("Sat splits", satSplits);
  COND_OUT("Sat splitting refutations", satSplitRefutations);
  SEPARATOR;

  COND_OUT("Pure propositional variables eliminated by SAT solver", satPureVarsEliminated);

  COND_OUT("InstGen generated clauses", instGenGeneratedClauses);
  COND_OUT("InstGen redundant clauses", instGenRedundantClauses);
  COND_OUT("InstGen kept clauses", instGenKeptClauses);
  COND_OUT("InstGen iterations", instGenIterations);

  COND_OUT("Max BFNT model size", maxBFNTModelSize);


  SEPARATOR;

  COND_OUT("Memory used [KB]", Allocator::getUsedMemory()/1024);
  out << "Time elapsed: ";
  Timer::printMSString(out,env.timer->elapsedMilliseconds());
  out << endl;
  out << "------------------------------\n";

  RSTAT_PRINT(out);
  DISPLAY_TRACE_STATS(out);
  out << "------------------------------\n";

#undef SEPARATOR
#undef COND_OUT

  if(env.options && env.options->timeStatistics()) {
    TimeCounter::printReport(out);
  }
}

const char* Statistics::phaseToString(ExecutionPhase p)
{
  switch(p) {
  case INITIALIZATION:
    return "Initialization";
  case PARSING:
    return "Parsing";
  case PROPERTY_SCANNING:
    return "Property scanning";
  case NORMALIZATION:
    return "Normalization";
  case SINE_SELECTION:
    return "SInE selection";
  case INCLUDING_THEORY_AXIOMS:
    return "Including theory axioms";
  case PREPROCESS_1:
    return "Preprocessing 1";
  case EQUALITY_PROPAGATION:
    return "Equality propagation";
  case PREDIACTE_DEFINITION_MERGING:
    return "Predicate definition merging";
  case EPR_PRESERVING_SKOLEMIZATION:
    return "EPR preserving skolemization";
  case PREDICATE_DEFINITION_INLINING:
    return "Predicate definition inlining";
  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "Unused predicate definition removal";
  case PREPROCESS_2:
    return "Preprocessing 2";
  case NAMING:
    return "Naming";
  case PREPROCESS_3:
    return "Preprocessing 3";
  case CLAUSIFICATION:
    return "Clausification";
  case FUNCTION_DEFINITION_ELIMINATION:
    return "Function definition elimination";
  case INEQUALITY_SPLITTING:
    return "Inequality splitting";
  case EQUALITY_RESOLUTION_WITH_DELETION:
    return "Equality resolution with deletion";
  case EQUALITY_PROXY:
    return "Equality proxy";
  case GENERAL_SPLITTING:
    return "General splitting";
  case HORN_REVEALING:
    return "Horn revealing";
  case SATURATION:
    return "Saturation";
  case FINALIZATION:
    return "Finalization";
  case UNKNOWN_PHASE:
    return "Unknown";
  default:
    ASSERTION_VIOLATION;
    return "Invalid ExecutionPhase value";
  }
}
