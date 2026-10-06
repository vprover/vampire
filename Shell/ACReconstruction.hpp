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
#include "Kernel/Inference.hpp"

#include <string>
#include <vector>

namespace Shell::ACReconstruction {

/** Capture the natural result at a preprocessing inference's creation site.
 * Only AC proof mode records this data; there is no general Clause hook. */
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

} // namespace Shell::ACReconstruction

#endif
