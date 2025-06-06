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
 * @file AnswerLiteralProcessors.hpp
 * Defines classes for removing clauses with invalid answer literals.
 */

#ifndef __AnswerLiteralProcessors__
#define __AnswerLiteralProcessors__

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

class SynthesisAnswerLiteralProcessor
: public ImmediateSimplificationEngine
{
public:
  Clause* simplify(Clause* premise) override;
private:
  bool unifyTermWithBothBranches(RobSubstitution* subst, TermList& t, TermList& branch1, TermList& branch2, TermList& res);
  bool unifyWithITE(RobSubstitution* subst, TermList& t1, TermList& t2, TermList& res);
  Literal* unifyWithITE(RobSubstitution* subst, Literal* l1, Literal* l2);
};

}

#endif // __AnswerLiteralProcessors__
