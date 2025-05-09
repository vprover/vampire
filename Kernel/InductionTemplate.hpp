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
 * @file InductionTemplate.hpp
 * Defines class InductionTemplate.
 */

#ifndef __InductionTemplate__
#define __InductionTemplate__

#include "Lib/Stack.hpp"

#include "Kernel/Inference.hpp"

using namespace std;

namespace Kernel {

/**
 * A formula template corresponding to (conditions → F[F_terms])
 * used as the unit for building induction formulas.
 */
struct InductionUnit
{
  InductionUnit(TermStack&& F_terms, LiteralStack&& conditions = LiteralStack());

  friend ostream& operator<<(ostream& out, const InductionUnit& u);

  TermStack F_terms;
  LiteralStack conditions;
};

/**
 * A formula template corresponding to ∀(hypotheses → conclusion)
 * used as a single case within an induction formula.
 */
struct InductionCase
{
  InductionCase(InductionUnit&& conclusion, Stack<InductionUnit>&& hypotheses = Stack<InductionUnit>());

  friend ostream& operator<<(ostream& out, const InductionCase& c);

  InductionUnit conclusion;
  Stack<InductionUnit> hypotheses;
};

/**
 * An induction formula template corresponding to ∀F(cases → conclusion).
 */
struct InductionTemplate
{
  InductionTemplate(Stack<InductionCase>&& cases, InductionUnit&& conclusion, InferenceRule rule);

  friend ostream& operator<<(ostream& out, const InductionTemplate& t);

  Stack<InductionCase> cases;
  InductionUnit conclusion;
  InferenceRule rule;
};

}

#endif // __InductionTemplate__
