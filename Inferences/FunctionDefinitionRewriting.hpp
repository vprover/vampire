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
 * It expands defined terms into their definition bodies, trying to
 * preserve the intended meaning of the definition. For example, if
 * a definition f(x) = if !C then t else ... defining f is clausified into
 * f(x) = t v C, we infer from clause D[f(s)] the new clause D[t] v C.
 * @see also FunctionDefinitionHandler.
 * Note that this replacement does not preserve refutational completeness.
 */

#ifndef __FunctionDefinitionRewriting__
#define __FunctionDefinitionRewriting__

#include "Forwards.hpp"

#include "DemodulationHelper.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Shell;

/**
 * Inference implementing function definition rewriting.
 * Function definitions are assumed to be available when saturation begins,
 * so there is only a forward version of the inference. Moreover, we use
 * a forward simplification variant to eagerly perform rewritings which
 * are also demodulations.
 */
class FunctionDefinitionRewriting
  : public GeneratingInferenceEngine
  {
public:
  FunctionDefinitionRewriting(SaturationAlgorithm& salg);
  ClauseIterator generateClauses(Clause *premise) override;

private:
  const SaturationAlgorithm& _salg;
  DemodulationHelper _helper;
};

/**
 * Simplifying version of the above inference, where we check if the rewriting
 * coincides with a demodulation under the current options and ordering.
 */
class FunctionDefinitionDemodulation
  : public ForwardSimplificationEngine
  {
public:
  FunctionDefinitionDemodulation(SaturationAlgorithm& salg);
  bool perform(Clause* cl, Clause*& replacement, ClauseIterator& premises) override;

private:
  const Ordering& _ord;
  const DemodulationHelper _helper;
  FunctionDefinitionHandler& _fnDefHandler;
};

}; // namespace Inferences

#endif /* __FunctionDefinitionRewriting__ */
