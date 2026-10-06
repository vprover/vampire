#ifndef __INFERENCE_REPLAY__
#define __INFERENCE_REPLAY__

#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Inference.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/Unit.hpp"

#include <memory>

namespace Shell {
class InferenceReplayer
{
public:
  void replayInference(Kernel::Unit* u);

  void makeInferenceEngine(Kernel::OrderingSP ord) {
    ASS(alg == nullptr);
    _ordering = ord;
    _problem = std::make_unique<Problem>();
    env.options->setSaturationAlgorithm(Shell::Options::SaturationAlgorithm::DISCOUNT);
    env.reconstruction = true;
    Ordering::unsetGlobalOrdering();
    alg.reset(Saturation::SaturationAlgorithm::createFromOptions(*_problem, *env.options));
    alg->setOrdering(_ordering);
  }

private:
  Kernel::OrderingSP _ordering;
  // The engine retains its Problem by reference. Own both for the entire
  // replay, and release the engine before the problem on destruction.
  std::unique_ptr<Kernel::Problem> _problem;
  std::unique_ptr<Saturation::SaturationAlgorithm> alg;

  void runBackwardsSimp(Inferences::BackwardSimplificationEngine* rule, ClauseStack context, Clause* goal);
  void runForwardsSimp(Inferences::ForwardSimplificationEngine* rule, ClauseStack context, Clause* goal);
  Clause* runGenerating(Inferences::GeneratingInferenceEngine* rule, ClauseStack context, Clause* goal);
  void removeAllActiveClauses();
};
}
#endif /* __INFERENCE_REPLAY__ */
