/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __Shell_TPTPReplayAnnotations__
#define __Shell_TPTPReplayAnnotations__

#include "Shell/InferenceRecorder.hpp"

#include <string>
#include <vector>

namespace Shell {
class InferenceReplayer;

namespace TPTPReplayAnnotations {

/** Annotation text and the natural inference result used to construct AC bridges.
 * The information pointer is borrowed from InferenceRecorder and must be used
 * before replaying another inference. */
struct ReplayAnnotation {
  std::string text;
  const InferenceRecorder::InferenceInformation* information = nullptr;
  std::vector<Kernel::Literal*> naturalLiterals;
};

/** Replay a clause inference, or recover its certificate directly for forward
 * subsumption resolution. Returns an empty annotation when replay is disabled. */
ReplayAnnotation replayedUnifier(Kernel::Unit* conclusion,
                                InferenceReplayer& replayer, bool replay);

/** Format the recorded scoped rectification data when replay is enabled. */
std::string rectificationInfo(Kernel::Unit* conclusion, bool replay);

/** Recover argument instantiations following AVATAR-definition rewrites. */
std::string avatarSplitInstantiationInfo(Kernel::Unit* conclusion);

} // namespace TPTPReplayAnnotations
} // namespace Shell

#endif
