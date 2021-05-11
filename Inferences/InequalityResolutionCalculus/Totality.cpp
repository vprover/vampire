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
 * @file Totality.cpp
 * Defines class Totality
 *
 */

#include "Totality.hpp"

#define TODO ASSERTION_VIOLATION

namespace Inferences {
namespace InequalityResolutionCalculus {

void Totality::attach(SaturationAlgorithm* salg) 
{ 
  TODO
}

void Totality::detach() 
{
  TODO
}

ClauseIterator Totality::generateClauses(Clause* premise) 
{
  TODO
}

  

#if VDEBUG
void Totality::setTestIndices(Stack<Indexing::Index*> const&) 
{
  TODO
}
#endif

template<class NumTraits> ClauseIterator Totality::generateClauses(Clause* clause, Literal* lit) const 
{
  TODO
}

} // namespace InequalityResolutionCalculus 
} // namespace Inferences 
