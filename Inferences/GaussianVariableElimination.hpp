#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "PolynomialNormalization.hpp"

namespace Inferences {
class GaussianVariableElimination : public MaybeImmediateSimplification {
public:
  CLASS_NAME(GaussianVariableElimination);
  USE_ALLOCATOR(GaussianVariableElimination);

  pair<Clause*, bool> simplify(Clause *cl, bool doCheckOrdering);

private:
  pair<Clause*, bool> rewrite(Clause &cl, TermList find, TermList replace,
                  unsigned skipLiteral, bool doOrderingCheck) const;
};
} // namespace Inferences
