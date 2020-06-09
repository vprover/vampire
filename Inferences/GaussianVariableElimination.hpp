#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"

namespace Inferences {
class GaussianVariableElimination : public ImmediateSimplificationEngine {
public:
  CLASS_NAME(GaussianVariableElimination);
  USE_ALLOCATOR(GaussianVariableElimination);

  Clause *simplify(Clause *cl);

private:
  Clause *rewrite(Clause &cl, TermList find, TermList replace,
                  unsigned skipLiteral) const;
};
} // namespace Inferences
