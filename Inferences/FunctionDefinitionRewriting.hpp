/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file FunctionDefinitionRewriting.hpp
 * Defines class FunctionDefinitionRewriting.
 */

#ifndef __FunctionDefinitionRewriting__
#define __FunctionDefinitionRewriting__

#include "Forwards.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Shell;

class FunctionDefinitionRewriting
  : public GeneratingInferenceEngine
  , public ForwardSimplificationEngine
  {
public:
  USE_ALLOCATOR(FunctionDefinitionRewriting);

  ClauseIterator generateClauses(Clause *premise) override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  static Clause *perform(
      Clause *rwClause, Literal *rwLiteral, TermList rwTerm,
      Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
      ResultSubstitutionSP subst, bool toplevelCheck,
      bool& isEqTautology, const Inference& inf, SaturationAlgorithm* salg = nullptr);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct GeneralizationsFn;
};

}; // namespace Inferences

#endif /* __FunctionDefinitionRewriting__ */
