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
 * @file Statistics.cpp
 * Implements proof-search statistics
 *
 * @since 02/01/2008 Manchester
 */

#include <iostream>

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/Environment.hpp"
#include "Lib/Timer.hpp"
#include "Lib/Allocator.hpp"
#include "SAT/Z3Interfacing.hpp"

#include "Shell/UIHelper.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Options.hpp"
#include "Statistics.hpp"
#include <chrono>


using namespace std;
using namespace Lib;
using namespace Saturation;
using namespace Shell;

string capitalize(string s) {
  if (!s.empty() && std::isalpha(s[0]) && !std::isupper(s[0])) {
    s[0] = std::toupper(s[0]);
  }
  return s;
}

void Statistics::explainRefutationNotFound(std::ostream& out)
{
  // should be a one-liner for each case!
  if (discardedNonRedundantClauses) {
    out << "Refutation not found, non-redundant clauses discarded\n";
  }
  else if (inferencesSkippedDueToColors) {
    out << "Refutation not found, inferences skipped due to colors\n";
  }
  else if(smtReturnedUnknown){
    out << "Refutation not found, SMT solver inside AVATAR returned Unknown\n";
  }
  else if (smtDidNotEvaluate) {
    out << "Refutation not found, SMT solver inside AVATAR failed to evaluate a literal\n";
  }
  else {
    out << "Refutation not found, incomplete strategy\n";
  }
}

void Statistics::print(std::ostream& out)
{
  if (env.options->statistics() != Options::Statistics::NONE) {

  SaturationAlgorithm::tryUpdateFinalClauseCount();

  addCommentSignForSZS(out);
  out << "------------------------------\n";
  addCommentSignForSZS(out);
  out << "Version: " << VERSION_STRING << endl;
#if VZ3
  addCommentSignForSZS(out);
  out << "Linked with Z3 " << Z3Interfacing::z3_full_version() << endl;
#endif

  addCommentSignForSZS(out);
  out << "Termination reason: ";
  switch(terminationReason) {
  case TerminationReason::REFUTATION:
    out << "Refutation\n";
    break;
  case TerminationReason::TIME_LIMIT:
    out << "Time limit\n";
    break;
  case TerminationReason::INSTRUCTION_LIMIT:
    out << "Instruction limit\n";
    break;
  case TerminationReason::MEMORY_LIMIT:
    out << "Memory limit\n";
    break;
  case TerminationReason::ACTIVATION_LIMIT:
    out << "Activation limit\n";
    break;
  case TerminationReason::REFUTATION_NOT_FOUND:
    explainRefutationNotFound(out);
    break;
  case TerminationReason::SATISFIABLE:
    out << "Satisfiable\n";
    break;
  case TerminationReason::UNKNOWN:
    out << "Unknown\n";
    break;
  case TerminationReason::INAPPROPRIATE:
    out << "Inappropriate\n";
    break;
  default:
    ASSERTION_VIOLATION;
  }
  if (phase!=ExecutionPhase::FINALIZATION) {
    addCommentSignForSZS(out);
    out << "Termination phase: " << phaseToString(phase) << endl;
  }

  if (env.options->statistics()==Options::Statistics::FULL) {

    struct Entry {
      string name;
      string total;
      string inproof;
    };
    struct Group {
      string name;
      Stack<Entry> entries;
    };
    Stack<Group> groups;

#define GROUP(gname) groups.push(Group { .name = gname, .entries = Stack<Entry>() });
#define ENTRY(ename, num) if (num) { groups.top().entries.push(Entry { .name = ename, .total = Int::toString(num), .inproof = "~" }); }

    auto outputInfRange = [&](InferenceRule first, InferenceRule last) {
      for (unsigned i : range(toNumber(first),toNumber(last))) {
        ASS_GE(inferenceCnts[i], inProofInferenceCnts[i]);
        if (!inferenceCnts[i]) { continue; }
        Entry e {
          .name = capitalize(ruleName(static_cast<InferenceRule>(i))),
          .total = Int::toString(inferenceCnts[i]),
          .inproof = Int::toString(inProofInferenceCnts[i])
        };
        groups.top().entries.push(e);
      }
    };

    GROUP("INPUT");
    outputInfRange(InferenceRule::INPUT, InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION);
    ENTRY("Input clauses", inputClauses);
    ENTRY("Input formulas", inputFormulas);

    GROUP("PREPROCESSING");
    outputInfRange(InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION, InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION_LAST);
    ENTRY("Introduced names", formulaNames);
    ENTRY("Introduced skolems", skolemFunctions);
    ENTRY("Pure predicates", purePredicates);
    ENTRY("Trivial predicates", trivialPredicates);
    ENTRY("Unused predicate definitions", unusedPredicateDefinitions);
    ENTRY("Function definitions", eliminatedFunctionDefinitions);
    ENTRY("Selected by SInE selection", selectedBySine);
    ENTRY("SInE iterations", sineIterations);
    ENTRY("Blocked clauses", blockedClauses);
    ENTRY("Split inequalities", splitInequalities);

    GROUP("SATURATION");
    ENTRY("Initial clauses", initialClauses);
    ENTRY("Generated clauses", generatedClauses);
    ENTRY("Activations started", activations);
    ENTRY("Active clauses", activeClauses);
    ENTRY("Passive clauses", passiveClauses);
    ENTRY("Extensionality clauses", extensionalityClauses);
    ENTRY("Final active clauses", finalActiveClauses);
    ENTRY("Final passive clauses", finalPassiveClauses);
    ENTRY("Final extensionality clauses", finalExtensionalityClauses);
    ENTRY("Discarded non-redundant clauses", discardedNonRedundantClauses);

    GROUP("SIMPLIFYING INFERENCES");
    outputInfRange(InferenceRule::GENERIC_SIMPLIFYING_INFERENCE, InferenceRule::GENERIC_SIMPLIFYING_INFERENCE_LAST);
    ENTRY("Duplicate literals", duplicateLiterals);
    ENTRY("Trivial inequalities", trivialInequalities);
    ENTRY("asg count", asgCnt);
    ENTRY("asg results not smaller than the premis", asgViolations);
    ENTRY("gve count", gveCnt);
    ENTRY("gve results not smaller than the premis", gveViolations);
    ENTRY("Evaluation count",         evaluationCnt);
    ENTRY("Evaluation results greater than premise", evaluationGreater);
    ENTRY("Evaluation results incomparable to premise", evaluationIncomp);

    GROUP("DELETION INFERENCES");
    ENTRY("Simple tautologies", simpleTautologies);
    ENTRY("Equational tautologies", equationalTautologies);
    ENTRY("Deep equational tautologies", deepEquationalTautologies);
    ENTRY("Forward subsumptions", forwardSubsumed);
    ENTRY("Backward subsumptions", backwardSubsumed);
    ENTRY("Forward ground joinable", forwardGroundJoinable);
    ENTRY("Fw demodulations to eq. taut.", forwardDemodulationsToEqTaut);
    ENTRY("Bw demodulations to eq. taut.", backwardDemodulationsToEqTaut);
    ENTRY("Fw subsumption demodulations to eq. taut.", forwardSubsumptionDemodulationsToEqTaut);
    ENTRY("Bw subsumption demodulations to eq. taut.", backwardSubsumptionDemodulationsToEqTaut);
    ENTRY("Inner rewrites to eq. taut.", innerRewritesToEqTaut);

    GROUP("GENERATING INFERENCES");
    outputInfRange(InferenceRule::GENERIC_GENERATING_INFERENCE, InferenceRule::GENERIC_GENERATING_INFERENCE_LAST);
    ENTRY("TheoryInstSimp",theoryInstSimp);
    ENTRY("TheoryInstSimpCandidates",theoryInstSimpCandidates);
    ENTRY("TheoryInstSimpTautologies",theoryInstSimpTautologies);
    ENTRY("TheoryInstSimpLostSolution",theoryInstSimpLostSolution);
    ENTRY("TheoryInstSimpEmptySubstitutions",theoryInstSimpEmptySubstitution);
    ENTRY("Introduced function definitions", introducedFunctionDefinitions);

    GROUP("THEORY AXIOMS");
    outputInfRange(InferenceRule::GENERIC_THEORY_AXIOM, InferenceRule::GENERIC_THEORY_AXIOM_LAST);

    // If any induction is applied, inductionApplication is non-zero
    GROUP("INDUCTION");
    ENTRY("MaxInductionDepth",maxInductionDepth);
    ENTRY("InductionApplications",inductionApplication);

    GROUP("REDUNDANCT INFERENCES");
    ENTRY("Skipped superposition", skippedSuperposition);
    ENTRY("Skipped resolution", skippedResolution);
    ENTRY("Due to ordering constraints", inferencesSkippedDueToOrderingConstraints);
    ENTRY("Due to AVATAR constraints", inferencesSkippedDueToAvatarConstraints);
    ENTRY("Due to literal constraints", inferencesSkippedDueToLiteralConstraints);
    ENTRY("Due to colors", inferencesSkippedDueToColors);
    ENTRY("Due to ordering aftercheck", inferencesBlockedDueToOrderingAftercheck);

    GROUP("AVATAR");
    ENTRY("Split clauses", splitClauses);
    ENTRY("Split components", splitComponents);
    ENTRY("Sat splitting refutations", satSplitRefutations);
    ENTRY("SMT fallbacks",smtFallbacks);

    //TODO record statistics for FMB

    //TODO record statistics for MiniSAT
    GROUP("SAT SOLVER");
    ENTRY("SAT solver clauses", satClauses);
    ENTRY("SAT solver unit clauses", unitSatClauses);
    ENTRY("SAT solver binary clauses", binarySatClauses);

    const string TOTALSTR = "TOTAL";
    const string PROOFSTR = "PROOF";
    const string COL_SEP = " | ";

    size_t enamemax = 0;
    size_t totalmax = TOTALSTR.length();
    size_t inproofmax = PROOFSTR.length();
    for (const auto& [gname, entries] : groups) {
      enamemax = max(enamemax, gname.length());
      for (const auto& [ename, total, inproof] : entries) {
        enamemax = max(enamemax, ename.length());
        totalmax = max(totalmax, total.length());
        inproofmax = max(inproofmax, inproof.length());
      }
    }

#define SEP_LINE addCommentSignForSZS(out); \
    out << string(enamemax + totalmax + COL_SEP.length() + (refutation ? inproofmax + COL_SEP.length() : 0) + 1, '-') << endl;

    SEP_LINE;

    for (const auto& [gname, entries] : groups) {
      if (entries.isEmpty()) { continue; }
      // header
      addCommentSignForSZS(out);
      out << setw(enamemax) << std::left << gname;
      out << COL_SEP << setw(totalmax) << std::right << TOTALSTR;
      if (refutation) {
        out << COL_SEP << setw(inproofmax) << std::right << PROOFSTR;
      }
      out << endl;
      SEP_LINE;

      // entries
      for (const auto& [ename, total, inproof] : entries) {
        ASS(total);
        ASS_GE(total, inproof);
        addCommentSignForSZS(out);
        out << setw(enamemax) << std::left << ename;
        out << COL_SEP << setw(totalmax) << std::right << total;
        if (refutation) {
          out << COL_SEP << setw(inproofmax) << std::right << inproof;
        }
        out << endl;
      }
      SEP_LINE;
    }
#undef SEP_LINE
#undef GROUP
#undef ENTRY
  }

  addCommentSignForSZS(out);
  out << "Time elapsed: ";
  Timer::printMSString(out,Timer::elapsedMilliseconds());
  out << endl;

  long peakMemKB = Lib::peakMemoryUsageKB();
  if (peakMemKB) {
    addCommentSignForSZS(out);
    out << "Peak memory usage: " << (peakMemKB >> 10) << " MB";
    out << endl;
  }

  Timer::updateInstructionCount();
  unsigned instr = Timer::elapsedMegaInstructions();
  if (instr) {
    addCommentSignForSZS(out);
    out << "Instructions burned: " << instr << " (million)";
    out << endl;
  }

  addCommentSignForSZS(out);
  out << "------------------------------\n";

  RSTAT_PRINT(out);
  addCommentSignForSZS(out);
  out << "------------------------------\n";

  } // if (env.options->statistics()!=Options::Statistics::NONE)

#if VTIME_PROFILING
  if (env.options && env.options->timeStatistics()) {
    TimeTrace::instance().printPretty(out);
  }
#endif // VTIME_PROFILING
}

void Statistics::reportUnit(Unit* u)
{
  if (u->isClause()) {
    generatedClauses++;
  }
  inferenceCnts[toNumber(u->inference().rule())]++;
}

void Statistics::reportProofStep(Unit* unit)
{
  inProofInferenceCnts[toNumber(unit->inference().rule())]++;
}

const char* Statistics::phaseToString(ExecutionPhase p)
{
  switch(p) {
  case ExecutionPhase::INITIALIZATION:
    return "Initialization";
  case ExecutionPhase::PARSING:
    return "Parsing";
  case ExecutionPhase::PROPERTY_SCANNING:
    return "Property scanning";
  case ExecutionPhase::NORMALIZATION:
    return "Normalization";
  case ExecutionPhase::SHUFFLING:
    return "shuffling";
  case ExecutionPhase::SINE_SELECTION:
    return "SInE selection";
  case ExecutionPhase::INCLUDING_THEORY_AXIOMS:
    return "Including theory axioms";
  case ExecutionPhase::PREPROCESS_1:
    return "Preprocessing 1";
  case ExecutionPhase::PREDIACTE_DEFINITION_MERGING:
    return "Predicate definition merging";
  case ExecutionPhase::PREDICATE_DEFINITION_INLINING:
    return "Predicate definition inlining";
  case ExecutionPhase::UNUSED_PREDICATE_DEFINITION_REMOVAL:
    return "Unused predicate definition removal";
  case ExecutionPhase::BLOCKED_CLAUSE_ELIMINATION:
    return "Blocked clause elimination";
  case ExecutionPhase::TWEE:
    return "Twee Goal Transformation";
  case ExecutionPhase::ANSWER_LITERAL:
    return "Answer literal addition";
  case ExecutionPhase::PREPROCESS_2:
    return "Preprocessing 2";
  case ExecutionPhase::NEW_CNF:
    return "NewCNF";
  case ExecutionPhase::NAMING:
    return "Naming";
  case ExecutionPhase::PREPROCESS_3:
    return "Preprocessing 3";
  case ExecutionPhase::CLAUSIFICATION:
    return "Clausification";
  case ExecutionPhase::FUNCTION_DEFINITION_ELIMINATION:
    return "Function definition elimination";
  case ExecutionPhase::INEQUALITY_SPLITTING:
    return "Inequality splitting";
  case ExecutionPhase::EQUALITY_RESOLUTION_WITH_DELETION:
    return "Equality resolution with deletion";
  case ExecutionPhase::EQUALITY_PROXY:
    return "Equality proxy";
  case ExecutionPhase::GENERAL_SPLITTING:
    return "General splitting";
  case ExecutionPhase::SATURATION:
    return "Saturation";
  case ExecutionPhase::FINALIZATION:
    return "Finalization";
  case ExecutionPhase::UNKNOWN_PHASE:
    return "Unknown";
  case ExecutionPhase::PREPROCESSING:
    return "BP Preprocessing ";
  case ExecutionPhase::SOLVING:
    return "Solving with Conflict Resolution";
  case ExecutionPhase::SAT_SOLVING:
	  return "SAT Solving";
  case ExecutionPhase::FMB_PREPROCESSING:
          return "Finite model building preprocessing";
  case ExecutionPhase::FMB_CONSTRAINT_GEN:
          return "Finite model building constraint generation";
  case ExecutionPhase::FMB_SOLVING:
          return "Finite model building SAT solving";
  default:
    ASSERTION_VIOLATION;
    return "Invalid ExecutionPhase value";
  }
}
