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
 * @file LiteralFactoring.cpp
 * Defines class LiteralFactoring
 *
 */

#include "LiteralFactoring.hpp"

#define TODO ASSERTION_VIOLATION

namespace Inferences {
namespace InequalityResolutionCalculus {

void LiteralFactoring::attach(SaturationAlgorithm* salg) 
{ 
  TODO
}

void LiteralFactoring::detach() 
{
  TODO
}

ClauseIterator LiteralFactoring::generateClauses(Clause* premise) 
{
  TODO
}

  

#if VDEBUG
void LiteralFactoring::setTestIndices(Stack<Indexing::Index*> const&) 
{
  TODO
}
#endif

template<class NumTraits> ClauseIterator LiteralFactoring::generateClauses(Clause* clause, Literal* lit) const 
{
  TODO
}

} // namespace InequalityResolutionCalculus 
} // namespace Inferences 
