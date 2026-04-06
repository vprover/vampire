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
#include <cadical.hpp>

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
  std::string cadicalVersion = CaDiCaL::Solver::signature();
  size_t dashPosition = cadicalVersion.find("-");
  if (dashPosition != string::npos) {
    cadicalVersion = cadicalVersion.substr(dashPosition + 1);
  }
  addCommentSignForSZS(out);
  out << "CaDiCaL version: " << cadicalVersion << endl;

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
      Entry(string name, string total, string inproof = string())
        : name(name), total(total), inproof(inproof) {}
      string name;
      string total;
      string inproof;
    };
    struct Group {
      Group(string name, bool infGroup = false) : name(name), infGroup(infGroup) {}
      void addEntry(string name, unsigned total, unsigned inproof = 0) {
        ASS(infGroup || inproof == 0);
        ASS(total);
        ASS_GE(total, inproof);
        entries.emplace(name, Int::toString(total), Int::toString(inproof));
      }

      string name;
      Stack<Entry> entries;
      bool infGroup;
    };
    Stack<Group> groups;

#define GROUP(name) groups.emplace(name);
#define ENTRY(name, num) if (num) { groups.top().addEntry(name, num); }

#define IPGROUP(name) groups.emplace(name, /*inproof=*/true);
#define IPENTRY(name, statpair) ASS_GE(statpair[TOTAL_CNT], statpair[INPROOF_CNT]); \
  if (statpair[TOTAL_CNT]) { groups.top().addEntry(name, statpair[TOTAL_CNT], statpair[INPROOF_CNT]); }

    IPGROUP("INPUT");
    for (unsigned i : range(toNumber(UnitInputType::AXIOM),toNumber(UnitInputType::MODEL_DEFINITION))) {
      IPENTRY(capitalize(inputTypeName(static_cast<UnitInputType>(i))), inputTypeCnts[i]);
    }

    auto outputInfGroup = [&](string name, InferenceRule first, InferenceRule last) {
      ASS_L(toNumber(first),toNumber(last));
      IPGROUP(name);
      for (unsigned i : range(toNumber(first),toNumber(last))) {
        IPENTRY(capitalize(ruleName(static_cast<InferenceRule>(i))), inferenceCnts[i]);
      }
    };

    outputInfGroup("FORMULA TRANSFORMATIONS", InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION, InferenceRule::GENERIC_FORMULA_CLAUSE_TRANSFORMATION_LAST);
    outputInfGroup("SIMPLIFYING INFERENCES", InferenceRule::GENERIC_SIMPLIFYING_INFERENCE, InferenceRule::GENERIC_SIMPLIFYING_INFERENCE_LAST);
    outputInfGroup("GENERATING INFERENCES", InferenceRule::GENERIC_GENERATING_INFERENCE, InferenceRule::GENERIC_GENERATING_INFERENCE_LAST);
    outputInfGroup("THEORY AXIOMS", InferenceRule::GENERIC_THEORY_AXIOM, InferenceRule::GENERIC_THEORY_AXIOM_LAST);
    outputInfGroup("AVATAR", InferenceRule::GENERIC_AVATAR_INFERENCE, InferenceRule::GENERIC_AVATAR_INFERENCE_LAST);
    outputInfGroup("MISCELLANEOUS INFERENCES", InferenceRule::GENERIC_GENERATING_INFERENCE_LAST, InferenceRule::GENERIC_AVATAR_INFERENCE);

    IPGROUP("CLAUSES/FORMULAS");
    IPENTRY("Input clauses", inputClauses);
    IPENTRY("Input formulas", inputFormulas);
    IPENTRY("Clauses", clauses);
    IPENTRY("Formulas", formulas);

    GROUP("PREPROCESSING");
    ENTRY("Introduced names", formulaNames);
    ENTRY("Introduced skolems", skolemFunctions);
    ENTRY("Pure predicates", purePredicates);
    ENTRY("Unused predicate definitions", unusedPredicateDefinitions);
    ENTRY("Function definitions", eliminatedFunctionDefinitions);
    ENTRY("Selected by SInE selection", selectedBySine);
    ENTRY("SInE iterations", sineIterations);
    ENTRY("Blocked clauses", blockedClauses);
    ENTRY("Split inequalities", splitInequalities);

    GROUP("SATURATION");
    ENTRY("Initial clauses", initialClauses);
    ENTRY("Activations started", activations);
    ENTRY("Active clauses", activeClauses);
    ENTRY("Passive clauses", passiveClauses);
    ENTRY("Extensionality clauses", extensionalityClauses);
    ENTRY("Final active clauses", finalActiveClauses);
    ENTRY("Final passive clauses", finalPassiveClauses);
    ENTRY("Final extensionality clauses", finalExtensionalityClauses);
    ENTRY("Discarded non-redundant clauses", discardedNonRedundantClauses);

    GROUP("SIMPLIFYING INFERENCES");
    ENTRY("Duplicate literals", duplicateLiterals);
    ENTRY("Trivial inequalities", trivialInequalities);

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

    GROUP("INDUCTION");
    ENTRY("MaxInductionDepth",maxInductionDepth);
    ENTRY("InductionApplications",inductionApplication);

    GROUP("REDUNDANT INFERENCES");
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

    // we create at most 3 cols, but the last 2 will have the same length
    size_t col1max = 0;
    size_t col2max = TOTALSTR.length();
    col2max = max(col2max, PROOFSTR.length());
    for (const auto& [gname, entries, infGroup] : groups) {
      col1max = max(col1max, gname.length());
      for (const auto& [ename, total, inproof] : entries) {
        col1max = max(col1max, ename.length());
        col2max = max(col2max, total.length());
        col2max = max(col2max, inproof.length());
      }
    }

#define SEP_LINE addCommentSignForSZS(out); \
    out << string(col1max + 2 * (col2max + COL_SEP.length()) + 1, '-') << endl;

    SEP_LINE;

    for (const auto& [gname, entries, infGroup] : groups) {
      if (entries.isEmpty()) { continue; }
      // header
      addCommentSignForSZS(out);
      out << setw(col1max) << std::left << gname;
      if (refutation && infGroup) {
        out << COL_SEP << setw(col2max) << std::right << PROOFSTR;
        out << COL_SEP << setw(col2max) << std::right << TOTALSTR;
      } else {
        out << COL_SEP << setw(2 * col2max + COL_SEP.length()) << std::right << TOTALSTR;
      }
      out << endl;
      SEP_LINE;

      // entries
      for (const auto& [ename, total, inproof] : entries) {
        addCommentSignForSZS(out);
        out << setw(col1max) << std::left << ename;
        if (refutation && infGroup) {
          out << COL_SEP << setw(col2max) << std::right << inproof;
          out << COL_SEP << setw(col2max) << std::right << total;
        } else {
          out << COL_SEP << setw(2 * col2max + COL_SEP.length()) << std::right << total;
        }
        out << endl;
      }
      SEP_LINE;
    }
#undef SEP_LINE
#undef GROUP
#undef ENTRY
#undef IPGROUP
#undef IPENTRY
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


  void Statistics::reportUnit(Unit* u, UnitCountCategory idx)
  {
    if (u->isClause()) {
      clauses[idx]++;
    } else {
      formulas[idx]++;
    }
    auto rule = u->inference().rule();
    if (rule == InferenceRule::INPUT) {
      inputTypeCnts[toNumber(u->inputType())][idx]++;
      if (u->isClause()) {
        inputClauses[idx]++;
      } else {
        inputFormulas[idx]++;
      }
    }
    inferenceCnts[toNumber(u->inference().rule())][idx]++;
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
