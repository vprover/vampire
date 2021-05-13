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
 * @file Superposition.cpp
 * Defines class Superposition
 *
 */

#include "Superposition.hpp"

#define TODO ASSERTION_VIOLATION

namespace Inferences {
namespace IRC {

void Superposition::attach(SaturationAlgorithm* salg) 
{ 
  TODO
}

void Superposition::detach() 
{
  TODO
}

ClauseIterator Superposition::generateClauses(Clause* premise) 
{
  TODO
}

  

#if VDEBUG
void Superposition::setTestIndices(Stack<Indexing::Index*> const&) 
{
  TODO
}
#endif

template<class NumTraits> ClauseIterator Superposition::generateClauses(Clause* clause, Literal* lit) const 
{
  TODO
}

} // namespace IRC 
} // namespace Inferences 
