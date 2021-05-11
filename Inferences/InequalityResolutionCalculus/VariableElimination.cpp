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
 * @file VariableElimination.cpp
 * Defines class VariableElimination
 *
 */

#include "VariableElimination.hpp"

#define TODO ASSERTION_VIOLATION

namespace Inferences {
namespace InequalityResolutionCalculus {

void VariableElimination::attach(SaturationAlgorithm* salg) 
{ 
  TODO
}

void VariableElimination::detach() 
{
  TODO
}

ClauseIterator VariableElimination::generateClauses(Clause* premise) 
{
  TODO
}

  

#if VDEBUG
void VariableElimination::setTestIndices(Stack<Indexing::Index*> const&) 
{
  TODO
}
#endif

template<class NumTraits> ClauseIterator VariableElimination::generateClauses(Clause* clause, Literal* lit) const 
{
  TODO
}

} // namespace InequalityResolutionCalculus 
} // namespace Inferences 
