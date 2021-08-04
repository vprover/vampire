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
 * @file FnDefRewriting.hpp
 * Defines class FnDefRewriting.
 */

#ifndef __FnDefRewriting__
#define __FnDefRewriting__

#include "Forwards.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Shell;

class FnDefRewriting
  : public GeneratingInferenceEngine
  , public ForwardSimplificationEngine
  {
public:
  CLASS_NAME(FnDefRewriting);
  USE_ALLOCATOR(FnDefRewriting);

  ClauseIterator generateClauses(Clause *premise) override;
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  static Clause *perform(
      Clause *rwClause, Literal *rwLiteral, TermList rwTerm,
      Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
      ResultSubstitutionSP subst,
      bool eqIsResult, bool& isEqTautology, const Inference& inf);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct GeneralizationsFn;
};

}; // namespace Inferences

#endif /* __FnDefRewriting__ */
