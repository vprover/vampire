/**
 * @file ClausifierDependencyFix.cpp
 *
 * Provides dummy implementations for some functions
 * referenced in code that is used in clausifier.
 */

#include "Forwards.hpp"

#include "Lib/Exception.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/AnswerExtractor.hpp"
#include "Shell/InterpolantMinimizer.hpp"

void Saturation::SaturationAlgorithm::tryUpdateFinalClauseCount()
{
}

Shell::InterpolantMinimizer::InterpolantMinimizer(bool, bool, bool, string)
{
}
Shell::InterpolantMinimizer::~InterpolantMinimizer()
{
}
Kernel::Formula* Shell::InterpolantMinimizer::getInterpolant(Kernel::Clause*)
{
  INVALID_OPERATION("not supported in clausifier");
}

void AnswerExtractor::tryOutputAnswer(Clause* refutation)
{
  INVALID_OPERATION("not supported in clausifier");
}
