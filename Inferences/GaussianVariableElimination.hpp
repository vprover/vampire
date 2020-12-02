/*
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
