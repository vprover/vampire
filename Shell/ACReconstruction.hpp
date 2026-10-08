/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __Shell_ACReconstruction__
#define __Shell_ACReconstruction__

#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Kernel/Inference.hpp"

#include <functional>
#include <ostream>
#include <string>
#include <vector>

namespace Shell::ACReconstruction {

/** Capture the natural result at a preprocessing inference's creation site.
 * Call sites gate this on the replay proof-extra status, which tstp-ac
 * requires; there is no general Clause hook. */
void recordPreprocessingOrder(Kernel::Clause* clause);

/**
 * Reconstruct the natural clause and its occurrence permutation to the
 * displayed conclusion. For forward subsumption resolution, core must contain
 * the natural literals recovered alongside its direct inference certificate;
 * for other rules, core and permutation must initially be empty.
 *
 * Returns true only for a complete, nonidentity permutation. Equality
 * orientation alone does not introduce a bridge. On false, output vectors
 * may contain partial reconstruction data and must not be printed.
 */
bool clauseOrderBridge(Kernel::Unit* conclusion, Kernel::InferenceRule rule,
                       const InferenceRecorder::InferenceInformation* information,
                       std::vector<Kernel::Literal*>& core,
                       std::vector<unsigned>& permutation);

/** Format the TSTP inference annotation for a reconstructed AC bridge. */
std::string acInference(const std::string& parent,
                        const std::vector<unsigned>& permutation);

/** Formats one full fof/tff/thf proof line from a node id, its formula and
 * its inference annotation. Callers bind the proof printer's rule role and
 * input type, which are not a concern of AC reconstruction. */
// The caller also adds the final clause's AVATAR split context.
using FofLine = std::function<std::string(const std::string& id, const std::string& formula,
                                          const std::string& inference)>;

/**
 * Print a proof node for clause @c us in the literal order in which its
 * inference constructed it. When that natural order differs from the
 * displayed clause, print a separate core node carrying the natural order,
 * followed by an AC permutation node deriving the displayed clause;
 * otherwise print the clause directly.
 *
 * @c orderRule drives the natural-order reconstruction, while @c printedRule
 * names the printed rule. Splitting has a custom inference/definition
 * annotation, but must use the same creation-order bridge as the ordinary
 * clause-printing path, hence the two rules are separate parameters.
 */
void printOrderedClause(std::ostream& out, Kernel::Unit* us,
                        Kernel::InferenceRule orderRule, Kernel::InferenceRule printedRule,
                        const std::string& inferenceStr, const FofLine& fofLine,
                        const InferenceRecorder::InferenceReplayAnnotation& replay = {});

} // namespace Shell::ACReconstruction

#endif
