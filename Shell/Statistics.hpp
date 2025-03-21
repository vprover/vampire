/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Statistics.hpp
 * Defines proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#ifndef __Statistics__
#define __Statistics__

#include <ostream>

#include "Forwards.hpp"
#include "Lib/Timer.hpp"
#include "Debug/Assertion.hpp"

extern const char *VERSION_STRING;

namespace Kernel {
class Unit;
}

namespace Shell {

using namespace Kernel;

/**
 * Class Statistics
 * @since 02/01/2008 Manchester
 */
class Statistics {
public:
  Statistics();

  void print(std::ostream& out);
  void explainRefutationNotFound(std::ostream& out);

  // Input
  /** number of input clauses */
  unsigned inputClauses;
  /** number of input formulas */
  unsigned inputFormulas;

  // Preprocessing
  /** number of formula names introduced during preprocessing */
  unsigned formulaNames;
  /** number of skolem functions (also predicates in FOOL) introduced during skolemization */
  unsigned skolemFunctions;
  /** number of initial clauses */
  unsigned initialClauses;
  /** number of inequality splittings performed */
  unsigned splitInequalities;
  /** number of pure predicates */
  unsigned purePredicates;
  /** number of trivial predicates */
  unsigned trivialPredicates;
  /** number of unused predicate definitions */
  unsigned unusedPredicateDefinitions;
  /** number of eliminated function definitions */
  unsigned functionDefinitions;
  /** number of formulas selected by SInE selector */
  unsigned selectedBySine;
  /** number of iterations before SInE reached fixpoint */
  unsigned sineIterations;
  /** number of detected blocked clauses */
  unsigned blockedClauses;

  // Generating inferences
  /** number of clauses generated by factoring*/
  unsigned factoring;
  /** number of clauses generated by binary resolution*/
  unsigned resolution;
  /** number of clauses generated by unit resulting resolution*/
  unsigned urResolution;
  /** number of clauses generated by constrained resolution */
  unsigned cResolution;
  /** number of clauses generated by forward superposition*/
  unsigned forwardSuperposition;
  /** number of clauses generated by backward superposition*/
  unsigned backwardSuperposition;
  /** number of clauses generated by self superposition*/
  unsigned cSelfSuperposition;
  /** number of clauses generated by forward superposition*/
  unsigned cForwardSuperposition;
  /** number of clauses generated by backward superposition*/
  unsigned cBackwardSuperposition;
  /** number of clauses generated by self superposition*/
  unsigned selfSuperposition;
  /** number of clauses generated by equality factoring*/
  unsigned equalityFactoring;
  /** number of clauses generated by equality resolution*/
  unsigned equalityResolution;
  /** number of clauses generated by forward extensionality resolution*/
  unsigned forwardExtensionalityResolution;
  /** number of clauses generated by backward extensionality resolution*/
  unsigned backwardExtensionalityResolution;
  /** number of theory inst simp **/
  unsigned theoryInstSimp;
  /** number of theoryInstSimp candidates **/
  unsigned theoryInstSimpCandidates;
  /** number of theoryInstSimp tautologies **/
  unsigned theoryInstSimpTautologies;
  /** number of theoryInstSimp solutions lost as we could not represent them **/
  unsigned theoryInstSimpLostSolution;
  /** number of theoryInstSimp application where an empty substitution was applied */
  unsigned theoryInstSimpEmptySubstitution;
  /** number of induction applications **/
  unsigned maxInductionDepth;
  unsigned structInduction;
  unsigned structInductionInProof;
  unsigned intInfInduction;
  unsigned intInfInductionInProof;
  unsigned intFinInduction;
  unsigned intFinInductionInProof;
  unsigned intDBInduction;
  unsigned intDBInductionInProof;
  unsigned intInfUpInduction;
  unsigned intInfUpInductionInProof;
  unsigned intFinUpInduction;
  unsigned intFinUpInductionInProof;
  unsigned intDBUpInduction;
  unsigned intDBUpInductionInProof;
  unsigned intInfDownInduction;
  unsigned intInfDownInductionInProof;
  unsigned intFinDownInduction;
  unsigned intFinDownInductionInProof;
  unsigned intDBDownInduction;
  unsigned intDBDownInductionInProof;
  unsigned inductionApplication;
  unsigned inductionApplicationInProof;
  unsigned generalizedInductionApplication;
  unsigned generalizedInductionApplicationInProof;
  /** number of argument congruences */
  unsigned argumentCongruence;
  unsigned narrow;
  unsigned forwardSubVarSup;
  unsigned backwardSubVarSup;
  unsigned selfSubVarSup;
  unsigned negativeExtensionality;
  unsigned primitiveInstantiations;
  unsigned choiceInstances;
  unsigned proxyEliminations;
  unsigned leibnizElims;
  unsigned booleanSimps;
  // Redundant inferences
  unsigned skippedSuperposition;
  unsigned skippedResolution;
  unsigned skippedEqualityResolution;
  unsigned skippedEqualityFactoring;
  unsigned skippedFactoring;
  unsigned skippedInferencesDueToOrderingConstraints;
  unsigned skippedInferencesDueToAvatarConstraints;
  unsigned skippedInferencesDueToLiteralConstraints;
  // Simplifying inferences
  /** number of duplicate literals deleted */
  unsigned duplicateLiterals;
  /** number of literals s |= s deleted */
  unsigned trivialInequalities;
  /** number of forward subsumption resolutions */
  unsigned forwardSubsumptionResolution;
  /** number of backward subsumption resolutions */
  unsigned backwardSubsumptionResolution;
  /** number of forward demodulations */
  unsigned forwardDemodulations;
  /** number of forward demodulations into equational tautologies */
  unsigned forwardDemodulationsToEqTaut;
  /** number of backward demodulations */
  unsigned backwardDemodulations;
  /** number of backward demodulations into equational tautologies */
  unsigned backwardDemodulationsToEqTaut;
  /** number of forward subsumption demodulations */
  unsigned forwardSubsumptionDemodulations;
  /** number of forward subsumption demodulations into equational tautologies */
  unsigned forwardSubsumptionDemodulationsToEqTaut;
  /** number of backward subsumption demodulations */
  unsigned backwardSubsumptionDemodulations;
  /** number of backward subsumption demodulations into equational tautologies */
  unsigned backwardSubsumptionDemodulationsToEqTaut;
  /** number of forward literal rewrites */
  unsigned forwardLiteralRewrites;
  /** number of condensations */
  unsigned condensations;
  /** number of global subsumptions */
  unsigned globalSubsumption;
  /** number of interpreted simplifications */
  unsigned interpretedSimplifications;

  /** how often did asg not simplify correctly. */
  unsigned asgViolations;
  /** applications of asg */
  unsigned asgCnt;

  /** how often did gve not simplify correctly. */
  unsigned gveViolations;
  /** applications of gve */
  unsigned gveCnt;

  /** number of evaluations that resulted in a incomparable literal */
  unsigned evaluationIncomp;
  /** number of evaluations that resulted in a greater literal */
  unsigned evaluationGreater;
  /** number of simplifications by PolynomialNormalizer */
  unsigned evaluationCnt;

  /** number of machine arithmetic overflows within the inequality resolution calculus specific rules */
  unsigned alascaVarElimKNonZeroCnt;
  unsigned alascaVarElimKSum;
  unsigned alascaVarElimKMax;

  /** number of (proper) inner rewrites */
  unsigned innerRewrites;
  /** number of inner rewrites into equational tautologies */
  unsigned innerRewritesToEqTaut;
  /** number of equational tautologies discovered by CC */
  unsigned deepEquationalTautologies;

  // Deletion inferences
  /** number of tautologies A \/ ~A */
  unsigned simpleTautologies;
  /** number of equational tautologies s=s */
  unsigned equationalTautologies;
  /** number of forward subsumed clauses */
  unsigned forwardSubsumed;
  /** number of backward subsumed clauses */
  unsigned backwardSubsumed;

  /** statistics of term algebra rules */
  unsigned taDistinctnessSimplifications;
  unsigned taDistinctnessTautologyDeletions;
  unsigned taInjectivitySimplifications;
  unsigned taNegativeInjectivitySimplifications;
  unsigned taAcyclicityGeneratedDisequalities;

  // Saturation
  unsigned activations = 0; // This is not a mere stat, it is also used for LRS estimation!
  /** all clauses ever occurring in the unprocessed queue */
  unsigned generatedClauses;
  /** all passive clauses */
  unsigned passiveClauses;
  /** all active clauses */
  unsigned activeClauses;
  /** all extensionality clauses */
  unsigned extensionalityClauses;

  unsigned discardedNonRedundantClauses;

  unsigned inferencesBlockedForOrderingAftercheck;

  bool smtReturnedUnknown;
  bool smtDidNotEvaluate;

  unsigned inferencesSkippedDueToColors;

  /** passive clauses at the end of the saturation algorithm run */
  unsigned finalPassiveClauses;
  /** active clauses at the end of the saturation algorithm run */
  unsigned finalActiveClauses;
  /** extensionality clauses at the end of the saturation algorithm run */
  unsigned finalExtensionalityClauses;
  unsigned splitClauses;
  unsigned splitComponents;
  // TODO currently not set, set it?
  unsigned uniqueComponents;
  /** Number of clauses generated for the SAT solver */
  unsigned satClauses;
  /** Number of unit clauses generated for the SAT solver */
  unsigned unitSatClauses;
  /** Number of binary clauses generated for the SAT solver */
  unsigned binarySatClauses;

  unsigned satSplits;
  unsigned satSplitRefutations;

  unsigned smtFallbacks;

  /** Number of pure variables eliminated by SAT solver */
  unsigned satPureVarsEliminated;

  /** termination reason */
  enum TerminationReason {
    /** refutation found */
    REFUTATION,
    /** satisfiability detected (saturated set built) */
    SATISFIABLE,
    /** saturation terminated but an incomplete strategy was used */
    REFUTATION_NOT_FOUND,
    /** inappropriate strategy **/
    INAPPROPRIATE,
    /** unknown termination reason */
    UNKNOWN,
    /** time limit reached */
    TIME_LIMIT,
    /** instruction limit reached */
    INSTRUCTION_LIMIT,
    /** memory limit reached */
    MEMORY_LIMIT,
    /** activation limit reached */
    ACTIVATION_LIMIT
  };
  friend std::ostream& operator<<(std::ostream& out, TerminationReason const& self)
  {
    switch (self) {
      case REFUTATION:
        return out << "REFUTATION";
      case SATISFIABLE:
        return out << "SATISFIABLE";
      case REFUTATION_NOT_FOUND:
        return out << "REFUTATION_NOT_FOUND";
      case INAPPROPRIATE:
        return out << "INAPPROPRIATE";
      case UNKNOWN:
        return out << "UNKNOWN";
      case TIME_LIMIT:
        return out << "TIME_LIMIT";
      case INSTRUCTION_LIMIT:
        return out << "INSTRUCTION_LIMIT";
      case MEMORY_LIMIT:
        return out << "MEMORY_LIMIT";
      case ACTIVATION_LIMIT:
        return out << "ACTIVATION_LIMIT";
    }
    ASSERTION_VIOLATION
  }
  /** termination reason */
  TerminationReason terminationReason;
  /** refutation, if any */
  Kernel::Unit *refutation;
  /** the saturated set of clauses, if any */
  Kernel::UnitList *saturatedSet;
  /** if problem is satisfiable and we obtained a model, contains its
   * representation; otherwise it is an empty string */
  std::string model;

  enum ExecutionPhase {
    /** Whatever happens before we start parsing the problem */
    INITIALIZATION,
    PARSING,
    /** Scanning for properties to be passed to preprocessing */
    PROPERTY_SCANNING,
    NORMALIZATION,
    SHUFFLING,
    SINE_SELECTION,
    INCLUDING_THEORY_AXIOMS,
    PREPROCESS_1,
    PREDIACTE_DEFINITION_MERGING,
    PREDICATE_DEFINITION_INLINING,
    UNUSED_PREDICATE_DEFINITION_REMOVAL,
    BLOCKED_CLAUSE_ELIMINATION,
    TWEE,
    ANSWER_LITERAL,
    PREPROCESS_2,
    NEW_CNF,
    NAMING,
    PREPROCESS_3,
    CLAUSIFICATION,
    FUNCTION_DEFINITION_ELIMINATION,
    INEQUALITY_SPLITTING,
    EQUALITY_RESOLUTION_WITH_DELETION,
    EQUALITY_PROXY,
    GENERAL_SPLITTING,
    SATURATION,
    /** The actual run of the conflict resolution algorithm */
    SOLVING,
    /** The actual run of the SAT solver*/
    SAT_SOLVING,
    PREPROCESSING,
    /** Whatever happens after the saturation algorithm finishes */
    FINALIZATION,
    FMB_PREPROCESSING,
    FMB_CONSTRAINT_GEN,
    FMB_SOLVING,
    UNKNOWN_PHASE
  };

  ExecutionPhase phase;

private:
  static const char* phaseToString(ExecutionPhase p);
}; // class Statistics

} // namespace Shell

#endif
