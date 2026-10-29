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
 * @file TPTPConstants.hpp
 * Names used in TPTP output: languages, roles, annotation types, statuses and the like.
 */

#ifndef __TPTPConstants__
#define __TPTPConstants__

namespace Shell {
namespace TPTPOutput {

/** TPTP languages, the keyword that starts each annotated formula. */
namespace Language {
inline constexpr const char* THF = "thf";
inline constexpr const char* TFF = "tff";
inline constexpr const char* TCF = "tcf";
inline constexpr const char* FOF = "fof";
inline constexpr const char* CNF = "cnf";
} // namespace Language

/** TPTP formula roles. */
namespace Role {
inline constexpr const char* AXIOM = "axiom";
inline constexpr const char* HYPOTHESIS = "hypothesis";
inline constexpr const char* DEFINITION = "definition";
inline constexpr const char* CONJECTURE = "conjecture";
inline constexpr const char* NEGATED_CONJECTURE = "negated_conjecture";
inline constexpr const char* PLAIN = "plain";
/** Not standard TPTP; Vampire reads it back as an extensionality axiom. */
inline constexpr const char* EXTENSIONALITY = "extensionality";
/** Not standard TPTP; Vampire-only, for the consequence-finding mode. */
inline constexpr const char* CLAIM = "claim";
} // namespace Role

/** Types of TPTP annotation terms, written as <type>(<arguments>). */
namespace AnnotationType {
inline constexpr const char* INFERENCE = "inference";
inline constexpr const char* INTRODUCED = "introduced";
inline constexpr const char* NEW_SYMBOLS = "new_symbols";
inline constexpr const char* STATUS = "status";
} // namespace AnnotationType

/** SZS statuses of inference steps, written as status(...). */
namespace Status {
/** Theorem: the conclusion follows from the premises. */
inline constexpr const char* THM = "thm";
/** Equivalent: the conclusion follows from the premises and vice versa. */
inline constexpr const char* EQV = "eqv";
/** Satisfiable: the conclusion is satisfiable if the premises are. */
inline constexpr const char* SAT = "sat";
/** Equisatisfiable: the conclusion is satisfiable iff the premises are. */
inline constexpr const char* ESA = "esa";
/** Counter-theorem: the negation of the conclusion follows from the premises. */
inline constexpr const char* CTH = "cth";
} // namespace Status

/** Origins of introduced formulas and symbols, written as introduced(...) and new_symbols(...). */
namespace Origin {
inline constexpr const char* DEFINITION = "definition";
inline constexpr const char* THEORY = "theory";
inline constexpr const char* SKOLEM = "skolem";
} // namespace Origin

/** Names of the propositional inferences in AVATAR proofs. */
namespace SatRule {
/** A propositional inference between SAT clauses. */
inline constexpr const char* RAT = "rat";
/** A SAT clause obtained from a first-order clause. */
inline constexpr const char* SAT_CONVERSION = "sat_conversion";
} // namespace SatRule

/** The TPTP constant false, also written for the empty clause. */
inline constexpr const char* FALSE_CONSTANT = "$false";
/** The TPTP constant true. */
inline constexpr const char* TRUE_CONSTANT = "$true";

/** File and name given for an input unit whose source is not known. */
inline constexpr const char* UNKNOWN_SOURCE = "unknown";

} // namespace TPTPOutput
} // namespace Shell

#endif // __TPTPConstants__
