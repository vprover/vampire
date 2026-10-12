#ifndef __INFERENCE_REPLAY__
#define __INFERENCE_REPLAY__

#include "Forwards.hpp"
#include "Lib/Stack.hpp"

#include <memory>

namespace Shell {
class InferenceReplayer
{
public:
  InferenceReplayer();
  ~InferenceReplayer();

  /** Replay only the recorded parents. The recorder accepts candidates that
   * reproduce the goal, including its variable names and literal occurrences. */
  void replayInference(Kernel::Unit* u);
  void makeInferenceEngine(Kernel::OrderingSP ordering);

private:
  // The engine retains its Problem by reference. Own both for the entire
  // replay, and release the engine before the problem on destruction.
  std::unique_ptr<Kernel::Problem> _problem;
  std::unique_ptr<Saturation::SaturationAlgorithm> _alg;

  void replayCondensation(Kernel::Clause* premise);
  void replayWitnessInference(Kernel::Clause* goal, const Kernel::ClauseStack& context);
  void replayParentlessAxiom(Kernel::Clause* goal);
  template<typename Engine> void runGenerating(const Kernel::ClauseStack& context);
  template<typename Engine> void runForwardsSimp(const Kernel::ClauseStack& context);
  template<typename Engine> void runBackwardsSimp(const Kernel::ClauseStack& context);
  void runBackwardsSimp(Inferences::BackwardSimplificationEngine& rule, const Kernel::ClauseStack& context);
  void runForwardsSimp(Inferences::ForwardSimplificationEngine& rule, const Kernel::ClauseStack& context);
  void runGenerating(Inferences::GeneratingInferenceEngine& rule, const Kernel::ClauseStack& context);
};
}
#endif /* __INFERENCE_REPLAY__ */
