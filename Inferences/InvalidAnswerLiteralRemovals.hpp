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
 * @file InvalidAnswerLiteralRemovals.hpp
 * Defines classes for removing clauses with invalid answer literals.
 */

#ifndef __InvalidAnswerLiteralRemovals__
#define __InvalidAnswerLiteralRemovals__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"

namespace Inferences {

/*
* Removes clauses containing answer literals with uncomputable symbols,
* as synthesized programs cannot include such symbols.
*/
class UncomputableAnswerLiteralRemoval
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

/*
* Removes clauses containing multiple answer literals,
* which is not allowed in program synthesis.
*/
class MultipleAnswerLiteralRemoval
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* cl) override;
};

/*
* Removes clauses containing answer literals that
* the user specified should be avoided.
*/
class UndesiredAnswerLiteralRemoval
: public ImmediateSimplificationEngine
{
public:
  UndesiredAnswerLiteralRemoval(const std::string& avoidThese);
  Clause* simplify(Clause* cl) override;
private:
  Clause* _avoiders;
};

// TODO(hzzv): rename the file?
class AnswerLiteralJoiner
: public ImmediateSimplificationEngine
{
public:
  ClauseIterator simplifyMany(Clause* cl) override;
  Clause* simplify(Clause* premise){ NOT_IMPLEMENTED; }
};

}

#endif // __InvalidAnswerLiteralRemovals__
