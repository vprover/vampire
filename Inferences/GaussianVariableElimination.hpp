#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "Kernel/Clause.hpp"
#include "LfpRule.hpp"

namespace Inferences {

class GaussianVariableElimination 
  : public SimplifyingGeneratingInference1 
{
public:
  CLASS_NAME(GaussianVariableElimination);
  USE_ALLOCATOR(GaussianVariableElimination);

  SimplifyingGeneratingInference1::Result simplify(Clause *cl, bool doCheckOrdering) override;

private:
  SimplifyingGeneratingInference1::Result rewrite(Clause &cl, TermList find, TermList replace,
                  unsigned skipLiteral, bool doOrderingCheck) const;
};

} // namespace Inferences
