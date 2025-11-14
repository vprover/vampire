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

#include <array>
#include <ostream>

#include "Forwards.hpp"
#include "Debug/Assertion.hpp"

#include "Kernel/Inference.hpp"

extern const char *VERSION_STRING;

namespace Kernel {
class Unit;
}

namespace Shell {

using namespace Kernel;

/** termination reason */
enum class TerminationReason {
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

enum class ExecutionPhase {
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
  /** Whatever happens after the saturation algorithm finishes */
  FINALIZATION,
  FMB_PREPROCESSING,
  FMB_CONSTRAINT_GEN,
  FMB_SOLVING
};

/**
 * Class Statistics
 * @since 02/01/2008 Manchester
 */
class Statistics {
public:
  enum UnitCountCategory { TOTAL_CNT = 0, INPROOF_CNT = 1 };

  void print(std::ostream& out);
  void explainRefutationNotFound(std::ostream& out);
  void reportUnit(Unit* u, UnitCountCategory idx);

  // Preprocessing
  /** number of formula names introduced during preprocessing */
  unsigned formulaNames = 0;
  /** number of skolem functions (also predicates in FOOL) introduced during skolemization */
  unsigned skolemFunctions = 0;
  /** number of initial clauses */
  unsigned initialClauses = 0;
  /** number of inequality splittings performed */
  unsigned splitInequalities = 0;
  /** number of pure predicates */
  unsigned purePredicates = 0;
  /** number of unused predicate definitions */
  unsigned unusedPredicateDefinitions = 0;
  /** number of eliminated function definitions */
  unsigned eliminatedFunctionDefinitions = 0;
  /** number of formulas selected by SInE selector */
  unsigned selectedBySine = 0;
  /** number of iterations before SInE reached fixpoint */
  unsigned sineIterations = 0;
  /** number of detected blocked clauses */
  unsigned blockedClauses = 0;

  // Induction
  unsigned maxInductionDepth = 0;
  unsigned inductionApplication = 0;

  // Redundant inferences
  unsigned skippedSuperposition = 0;
  unsigned skippedResolution = 0;
  unsigned inferencesSkippedDueToOrderingConstraints = 0;
  unsigned inferencesSkippedDueToAvatarConstraints = 0;
  unsigned inferencesSkippedDueToLiteralConstraints = 0;
  unsigned inferencesBlockedDueToOrderingAftercheck = 0;
  unsigned inferencesSkippedDueToColors = 0;

  // Simplifying inferences
  /** number of duplicate literals deleted */
  unsigned duplicateLiterals = 0;
  /** number of literals s != s deleted */
  unsigned trivialInequalities = 0;
  /** number of forward demodulations into equational tautologies */
  unsigned forwardDemodulationsToEqTaut = 0;
  /** number of backward demodulations into equational tautologies */
  unsigned backwardDemodulationsToEqTaut = 0;
  /** number of forward subsumption demodulations into equational tautologies */
  unsigned forwardSubsumptionDemodulationsToEqTaut = 0;
  /** number of backward subsumption demodulations into equational tautologies */
  unsigned backwardSubsumptionDemodulationsToEqTaut = 0;

  // Deletion inferences
  /** number of tautologies A \/ ~A */
  unsigned simpleTautologies = 0;
  /** number of equational tautologies s=s */
  unsigned equationalTautologies = 0;
  /** number of forward subsumed clauses */
  unsigned forwardSubsumed = 0;
  /** number of backward subsumed clauses */
  unsigned backwardSubsumed = 0;
  /** number of forward ground joinable clauses */
  unsigned forwardGroundJoinable = 0;
  /** number of term algebra distinctness tautology deletions */
  unsigned taDistinctnessTautologyDeletions = 0;
  /** number of inner rewrites into equational tautologies */
  unsigned innerRewritesToEqTaut = 0;
  /** number of equational tautologies discovered by CC */
  unsigned deepEquationalTautologies = 0;

  // Saturation
  unsigned activations = 0; // NOTE: This is not a mere stat, it is also used for LRS estimation!

  /** all passive clauses */
  unsigned passiveClauses = 0;
  /** all active clauses */
  unsigned activeClauses = 0;
  /** all extensionality clauses */
  unsigned extensionalityClauses = 0;

  unsigned discardedNonRedundantClauses = 0;

  bool smtReturnedUnknown = false;
  bool smtDidNotEvaluate = false;

  /** passive clauses at the end of the saturation algorithm run */
  unsigned finalPassiveClauses = 0;
  /** active clauses at the end of the saturation algorithm run */
  unsigned finalActiveClauses = 0;
  /** extensionality clauses at the end of the saturation algorithm run */
  unsigned finalExtensionalityClauses = 0;
  unsigned splitClauses = 0;
  unsigned splitComponents = 0;

  /** Number of clauses generated for the SAT solver */
  unsigned satClauses = 0;
  /** Number of unit clauses generated for the SAT solver */
  unsigned unitSatClauses = 0;
  /** Number of binary clauses generated for the SAT solver */
  unsigned binarySatClauses = 0;

  unsigned satSplitRefutations = 0;

  unsigned smtFallbacks = 0;

  friend std::ostream& operator<<(std::ostream& out, TerminationReason const& self)
  {
    switch (self) {
      case TerminationReason::REFUTATION:
        return out << "REFUTATION";
      case TerminationReason::SATISFIABLE:
        return out << "SATISFIABLE";
      case TerminationReason::REFUTATION_NOT_FOUND:
        return out << "REFUTATION_NOT_FOUND";
      case TerminationReason::INAPPROPRIATE:
        return out << "INAPPROPRIATE";
      case TerminationReason::UNKNOWN:
        return out << "UNKNOWN";
      case TerminationReason::TIME_LIMIT:
        return out << "TIME_LIMIT";
      case TerminationReason::INSTRUCTION_LIMIT:
        return out << "INSTRUCTION_LIMIT";
      case TerminationReason::MEMORY_LIMIT:
        return out << "MEMORY_LIMIT";
      case TerminationReason::ACTIVATION_LIMIT:
        return out << "ACTIVATION_LIMIT";
    }
    ASSERTION_VIOLATION
  }
  /** termination reason */
  TerminationReason terminationReason = TerminationReason::UNKNOWN;
  /** refutation, if any */
  Kernel::Unit *refutation = nullptr;
  /** the saturated set of clauses, if any */
  Kernel::UnitList *saturatedSet = nullptr;
  /** if problem is satisfiable and we obtained a model, contains its
   * representation; otherwise it is an empty string */
  std::string model;

  ExecutionPhase phase = ExecutionPhase::INITIALIZATION;

private:
  static const char* phaseToString(ExecutionPhase p);

  /** A pair counting the total and in-proof value of a statistic. */
  typedef std::array<unsigned,2> StatPair;

  /** number of input clauses */
  StatPair inputClauses;
  /** number of input formulas */
  StatPair inputFormulas;
  /** all clauses */
  StatPair clauses;
  /** all formulas */
  StatPair formulas;
  /** inference counts indexed by InferenceRule */
  std::array<StatPair, toNumber(InferenceRule::GENERIC_THEORY_AXIOM_LAST)> inferenceCnts = {};
  /** input types indexed by UnitInputType */
  std::array<StatPair, toNumber(UnitInputType::MODEL_DEFINITION)> inputTypeCnts = {};
}; // class Statistics

} // namespace Shell

#endif
