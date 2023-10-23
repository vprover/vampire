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
 * @file InvalidAnswerLiteralRemoval.hpp
 * Defines class InvalidAnswerLiteral.
 */

#ifndef __InvalidAnswerLiteralRemoval__
#define __InvalidAnswerLiteralRemoval__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

/*   
* Removes clauses containing answer literals with uncomputable symbols, 
* as synthesized programs cannot include such symbols.
*/
class InvalidAnswerLiteralRemoval
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(InvalidAnswerLiteralRemoval);
  USE_ALLOCATOR(InvalidAnswerLiteralRemoval);

  Clause* simplify(Clause* cl) override;
};

}

#endif // __InvalidAnswerLiteralRemoval__
