/**
 * @file ClausifierDependencyFix.cpp
 *
 * Provides dummy implementations for some functions
 * referenced in code that is used in clausifier.
 */

#include "Forwards.hpp"

#include "Lib/Exception.hpp"

#include "Kernel/LiteralSelector.hpp"

#include "Saturation/SaturationAlgorithm.hpp"
#include "Shell/AnswerExtractor.hpp"
#include "Shell/InterpolantMinimizer.hpp"

void LiteralSelector::reversePredicatePolarity(unsigned pred, bool reverse)
{
}

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

AnswerLiteralManager* AnswerLiteralManager::getInstance()
{
  INVALID_OPERATION("answer literals not supported in clausifier");
}

void AnswerLiteralManager::addAnswerLiterals(UnitList*& units)
{
  INVALID_OPERATION("answer literals not supported in clausifier");
}
