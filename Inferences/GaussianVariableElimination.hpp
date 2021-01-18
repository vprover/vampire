
  /*
   * File GaussianVariableElimination.hpp.
   *
   * This file is part of the source code of the software program
   * Vampire. It is protected by applicable
   * copyright laws.
   *
   * This source code is distributed under the licence found here
   * https://vprover.github.io/license.html
   * and in the source directory
   */

#include "InferenceEngine.hpp"
#include "Lib/Set.hpp"
#include "Kernel/Clause.hpp"
#include "LfpRule.hpp"
#include "Kernel/Rebalancing.hpp"

namespace Inferences {

class GaussianVariableElimination 
  : public SimplifyingGeneratingInference1 
{
  const bool _generateGuards;
public:
  CLASS_NAME(GaussianVariableElimination);
  USE_ALLOCATOR(GaussianVariableElimination);

  GaussianVariableElimination(bool generateGuards) : _generateGuards(generateGuards) {}
  SimplifyingGeneratingInference1::Result simplify(Clause *cl, bool doCheckOrdering) override;
private:
  SimplifyingGeneratingInference1::Result rewrite(Clause &cl, TermList find, Kernel::Rebalancing::InversionResult replace,
                  unsigned skipLiteral, bool doOrderingCheck) const;

};

} // namespace Inferences
