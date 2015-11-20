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

#include "Shell/UIHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#if GNUMP
#include "Kernel/Assignment.hpp"
#include "Kernel/Constraint.hpp"
#endif

#include "Options.hpp"
#include "Statistics.hpp"


using namespace std;
using namespace Lib;
using namespace Saturation;
using namespace Shell;

/**
 * Initialise statistics.
 * @since 02/01/2008 Manchester
 */
Statistics::Statistics()
  : inputClauses(0),
    inputFormulas(0),
    hasTypes(false),
    formulaNames(0),
    initialClauses(0),
    splitInequalities(0),
    purePredicates(0),
    trivialPredicates(0),
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
    forwardExtensionalityResolution(0),
    backwardExtensionalityResolution(0),
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
    generatedClauses(0),
    passiveClauses(0),
    activeClauses(0),
    extensionalityClauses(0),
    discardedNonRedundantClauses(0),
    inferencesSkippedDueToColors(0),
    finalPassiveClauses(0),
    finalActiveClauses(0),
    finalExtensionalityClauses(0),
    splitClauses(0),
    splitComponents(0),
    uniqueComponents(0),
    satClauses(0),
    unitSatClauses(0),
    binarySatClauses(0),
    learntSatClauses(0),
    learntSatLiterals(0),

    satSplits(0),
    satSplitRefutations(0),

    satLingelingAssumptions(0),
    satLingelingClauses(0),
    satLingelingVariables(0),
    satLingelingSATCalls(0),
    /**TODO Remove the next var*/
    satTWLClauseCount(0),
    satTWLVariablesCount(0),
    satTWLSATCalls(0),

    instGenGeneratedClauses(0),
    instGenRedundantClauses(0),
    instGenKeptClauses(0),
    instGenIterations(0),

    maxBFNTModelSize(0),

    satPureVarsEliminated(0),
    terminationReason(UNKNOWN),
    refutation(0),
    saturatedSet(0),
    phase(INITIALIZATION)
{
} // Statistics::Statistics

/**
 * In the CASC mode output "% " so that the following line will be considered a comment.
 * @author Andrei Voronkov
 * @since 03/06/2012 Manchester
 */
void Statistics::addCommentIfCASC(ostream& out)
{
  if (UIHelper::szsOutput) {
    out << "% ";
  }
} // Statistics::addCommentIfCASC

void Statistics::print(ostream& out)
{
  if (env.options->statistics()==Options::Statistics::NONE) {
    return;
  }

  SaturationAlgorithm::tryUpdateFinalClauseCount();

  bool separable=false;
#define HEADING(text,num) if (num) { addCommentIfCASC(out); out << ">>> " << (text) << endl;}
#define COND_OUT(text, num) if (num) { addCommentIfCASC(out); out << (text) << ": " << (num) << endl; separable = true; }
#define SEPARATOR if (separable) {   addCommentIfCASC(out); out << endl; separable = false; }

  addCommentIfCASC(out);
  out << "------------------------------\n";
  addCommentIfCASC(out);
  out << "Version: " << VERSION_STRING << endl;

  addCommentIfCASC(out);
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
    if (env.statistics->discardedNonRedundantClauses) {
      out << "Refutation not found, non-redundant clauses discarded";
    }
    else {
      out << "Refutation not found, incomplete strategy";
    }
    break;
  case Statistics::SATISFIABLE:
    out << "Satisfiable";
    break;
  case Statistics::SAT_SATISFIABLE:
    out << "SAT Satisfiable";
    break;
  case Statistics::SAT_UNSATISFIABLE: 
    out << "SAT Unsatisfiable";
    break;
  case Statistics::UNKNOWN:
    out << "Unknown";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  out << endl;
  if (phase!=FINALIZATION) {
    addCommentIfCASC(out);
    out << "Termination phase: " << phaseToString(phase) << endl;
  }
  out << endl;

  if (env.options->statistics()==Options::Statistics::FULL) {

  HEADING("Input",inputClauses+inputFormulas);
  COND_OUT("Input clauses", inputClauses);
  COND_OUT("Input formulas", inputFormulas);

  HEADING("Preprocessing",formulaNames+purePredicates+trivialPredicates+
    unusedPredicateDefinitions+functionDefinitions+selectedBySine+
    sineIterations+splitInequalities);
  COND_OUT("Introduced names",formulaNames);
  COND_OUT("Pure predicates", purePredicates);
  COND_OUT("Trivial predicates", trivialPredicates);
  COND_OUT("Unused predicate definitions", unusedPredicateDefinitions);
  COND_OUT("Function definitions", functionDefinitions);
  COND_OUT("Selected by SInE selection", selectedBySine);
  COND_OUT("SInE iterations", sineIterations);
  COND_OUT("Split inequalities", splitInequalities);
  SEPARATOR;

  HEADING("Saturation",activeClauses+passiveClauses+extensionalityClauses+
      generatedClauses+finalActiveClauses+finalPassiveClauses+finalExtensionalityClauses+
      discardedNonRedundantClauses+inferencesSkippedDueToColors);
  COND_OUT("Initial clauses", initialClauses);
  COND_OUT("Generated clauses", generatedClauses);
  COND_OUT("Active clauses", activeClauses);
  COND_OUT("Passive clauses", passiveClauses);
  COND_OUT("Extensionality clauses", extensionalityClauses);
  COND_OUT("Final active clauses", finalActiveClauses);
  COND_OUT("Final passive clauses", finalPassiveClauses);
  COND_OUT("Final extensionality clauses", finalExtensionalityClauses);
  COND_OUT("Discarded non-redundant clauses", discardedNonRedundantClauses);
  COND_OUT("Inferences skipped due to colors", inferencesSkippedDueToColors);
  SEPARATOR;


  HEADING("Simplifying Inferences",duplicateLiterals+trivialInequalities+
      forwardSubsumptionResolution+backwardSubsumptionResolution+
      forwardDemodulations+backwardDemodulations+forwardLiteralRewrites+
      condensations+globalSubsumption+evaluations);
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
  //COND_OUT("Interpreted simplifications", interpretedSimplifications);
  SEPARATOR;

  HEADING("Deletion Inferences",simpleTautologies+equationalTautologies+
      forwardSubsumed+backwardSubsumed+forwardDemodulationsToEqTaut+
      backwardDemodulationsToEqTaut);
  COND_OUT("Simple tautologies", simpleTautologies);
  COND_OUT("Equational tautologies", equationalTautologies);
  COND_OUT("Forward subsumptions", forwardSubsumed);
  COND_OUT("Backward subsumptions", backwardSubsumed);
  COND_OUT("Fw demodulations to eq. taut.", forwardDemodulationsToEqTaut);
  COND_OUT("Bw demodulations to eq. taut.", backwardDemodulationsToEqTaut);
  SEPARATOR;

  HEADING("Generating Inferences",resolution+urResolution+factoring+
      forwardSuperposition+backwardSuperposition+selfSuperposition+
      equalityFactoring+equalityResolution+forwardExtensionalityResolution+
      backwardExtensionalityResolution);
  COND_OUT("Binary resolution", resolution);
  COND_OUT("Unit resulting resolution", urResolution);
  COND_OUT("Factoring", factoring);
  COND_OUT("Forward superposition", forwardSuperposition);
  COND_OUT("Backward superposition", backwardSuperposition);
  COND_OUT("Self superposition", selfSuperposition);
  COND_OUT("Equality factoring", equalityFactoring);
  COND_OUT("Equality resolution", equalityResolution);
  COND_OUT("Fw extensionality resolution", forwardExtensionalityResolution);
  COND_OUT("Bw extensionality resolution", backwardExtensionalityResolution);
  SEPARATOR;

  HEADING("AVATAR",splitClauses+splitComponents+uniqueComponents+satSplits+
        satSplitRefutations);
  COND_OUT("Split clauses", splitClauses);
  COND_OUT("Split components", splitComponents);
  COND_OUT("Unique components", uniqueComponents);
  COND_OUT("Sat splits", satSplits);
  COND_OUT("Sat splitting refutations", satSplitRefutations);
  SEPARATOR;

  HEADING("Instance Generation",instGenGeneratedClauses+instGenRedundantClauses+
       instGenKeptClauses+instGenIterations);
  COND_OUT("InstGen generated clauses", instGenGeneratedClauses);
  COND_OUT("InstGen redundant clauses", instGenRedundantClauses);
  COND_OUT("InstGen kept clauses", instGenKeptClauses);
  COND_OUT("InstGen iterations", instGenIterations);
  SEPARATOR;

  //TODO record statistics for FMB
  HEADING("Model Building",maxBFNTModelSize);
  COND_OUT("Max BFNT model size", maxBFNTModelSize);
  SEPARATOR;


  //TODO record statistics for MiniSAT
  HEADING("SAT Solver Statistics",satLingelingAssumptions+satLingelingVariables+
        satLingelingClauses+satLingelingClauses+satLingelingClauses+
        satLingelingSATCalls+satTWLClauseCount+satTWLVariablesCount+
        satTWLSATCalls+satClauses+unitSatClauses+binarySatClauses+
        learntSatClauses+learntSatLiterals+satPureVarsEliminated);
  COND_OUT("SAT solver clauses", satClauses);
  COND_OUT("SAT solver unit clauses", unitSatClauses);
  COND_OUT("SAT solver binary clauses", binarySatClauses);
  COND_OUT("TWL SAT solver learnt clauses", learntSatClauses);
  COND_OUT("TWL SAT solver learnt literals", learntSatLiterals);
  COND_OUT("Lingeling assumptions", satLingelingAssumptions);
  COND_OUT("Lingeling vampire count variables", satLingelingVariables);
  COND_OUT("Lingeling vampire count clauses", satLingelingClauses);
  COND_OUT("Lingeling calls for satisfiability", satLingelingSATCalls);
  COND_OUT("TWLsolver clauses", satTWLClauseCount);
  COND_OUT("TWLsolver variables", satTWLVariablesCount);
  COND_OUT("TWLsolver calls for satisfiability", satTWLSATCalls);
  COND_OUT("Pure propositional variables eliminated by SAT solver", satPureVarsEliminated);
  SEPARATOR;

  }

  COND_OUT("Memory used [KB]", Allocator::getUsedMemory()/1024);

  addCommentIfCASC(out);
  out << "Time elapsed: ";
  Timer::printMSString(out,env.timer->elapsedMilliseconds());
  out << endl;
  addCommentIfCASC(out);
  out << "------------------------------\n";

  RSTAT_PRINT(out);
  addCommentIfCASC(out);
  out << "------------------------------\n";

#undef SEPARATOR
#undef COND_OUT

  if (env.options && env.options->timeStatistics()) {
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
  case PREDICATE_DEFINITION_INLINING:
    return "Predicate definition inlining";
  case UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "Unused predicate definition removal";
  case PREPROCESS_2:
    return "Preprocessing 2";
  case NEW_CNF:
    return "NewCNF";
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
  case SATURATION:
    return "Saturation";
  case FINALIZATION:
    return "Finalization";
  case UNKNOWN_PHASE:
    return "Unknown";
  case PREPROCESSING: 
    return "BP Preprocessing ";
  case SOLVING:
    return "Solving with Conflict Resolution";
  case SAT_SOLVING:
	  return "SAT Solving";
  case FMB_PREPROCESSING:
          return "Finite model building preprocessing";
  case FMB_CONSTRAINT_GEN:
          return "Finite model building constraint generation";
  case FMB_SOLVING:
          return "Finite model building SAT solving";
  default:
    ASSERTION_VIOLATION;
    return "Invalid ExecutionPhase value";
  }
}
