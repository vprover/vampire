#ifndef __INFERENCE_REPLAY__
#define __INFERENCE_REPLAY__


#include "Debug/Assertion.hpp"
#include "Forwards.hpp"
#include "Kernel/Inference.hpp"
#include "Saturation/SaturationAlgorithm.hpp"

#include "Kernel/Unit.hpp"

#include <ostream>
namespace Shell{
class InferenceReplayer
{
    
    public:

    InferenceReplayer(std::ostream& output) : out(&output) {}

    void replayInference(Kernel::Unit* u);

    void makeInferenceEngine(Kernel::OrderingSP ord) {
        ASS(alg == nullptr);
        _ordering = ord;
        Problem p;
        env.options->setSaturationAlgorithm(Shell::Options::SaturationAlgorithm::DISCOUNT);
        env.reconstruction = true;
        alg = Saturation::SaturationAlgorithm::createFromOptions(p, *env.options);
        alg->setOrdering(_ordering);   
    }
    
    private:
    Kernel::OrderingSP _ordering;
    std::ostream* out = nullptr;
    Indexing::SaturationAlgorithm* alg = nullptr;

    static bool isClauseRule(const InferenceRule &rule);
    void runBackwardsSimp(Inferences::BackwardSimplificationEngine* rule, ClauseStack context, Clause* goal);
    void runForwardsSimp(Inferences::ForwardSimplificationEngine* rule, ClauseStack context, Clause* goal);
    Clause* runGenerating(Inferences::GeneratingInferenceEngine* rule, ClauseStack context, Clause* goal);
    void removeAllActiveClauses();
};
}
#endif /* __INFERENCE_REPLAY__ */