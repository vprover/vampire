/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __INFERENCE_REPLAY__
#define __INFERENCE_REPLAY__

#include "Forwards.hpp"

#include <memory>

namespace Inferences { struct InferenceReplayInformation; }

namespace Shell {
class InferenceReplayer
{
public:
  InferenceReplayer();
  ~InferenceReplayer();

  /** Replay only the recorded parents, accepting candidates that reproduce the
   * goal, including its variable names and literal occurrences.
   * On success, replace the goal's proof extra and return a borrowed pointer to
   * it, valid until replacement or clause destruction. On failure, return
   * nullptr and leave the existing extra untouched. */
  const Inferences::InferenceReplayInformation* replayInference(Kernel::Unit* u);
  void makeInferenceEngine(Kernel::OrderingSP ordering);

private:
  // The engine retains its Problem by reference. Own both for the entire
  // replay, and release the engine before the problem on destruction.
  std::unique_ptr<Kernel::Problem> _problem;
  std::unique_ptr<Saturation::SaturationAlgorithm> _alg;

  template<typename Engine> void runInference(const Kernel::Unit& unit);
  void runForwardsSimp(Inferences::ForwardSimplificationEngine& rule, Kernel::Clause* premise);
  void runGenerating(Inferences::GeneratingInferenceEngine& rule, Kernel::Clause* premise);
};
}
#endif /* __INFERENCE_REPLAY__ */
