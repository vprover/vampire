#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"

namespace Inferences {
class RebalancingElimination : public ImmediateSimplificationEngine {
public:
  CLASS_NAME(RebalancingElimination);
  USE_ALLOCATOR(RebalancingElimination);

  Clause *simplify(Clause *cl);

private:
  Clause *rewrite(const Clause &cl, TermList find, TermList replace,
                  unsigned skipLiteral) const;
};
} // namespace Inferences
