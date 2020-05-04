#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"

namespace Inferences {
  class RebalancingElimination 
  : public ImmediateSimplificationEngine {

  public:
  Clause* simplify(Clause* cl);
  
  };
}
