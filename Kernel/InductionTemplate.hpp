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

namespace Kernel {

using VStack = Stack<unsigned>;

/**
 * A formula template corresponding to the unit for building induction formulas,
 * of the form (∀ x_1,...,x_k.(l_1 ⋀ ... ⋀ l_m)) → F[t_1,...,t_n], where
 * F is a free second-order variable of arity n,
 * @b F_terms is the list of terms t_1,...,t_n,
 * @b conditions is the list of literals l_1,...,l_m, and
 * @b condUnivVars is the list of variables x_1,...,x_k.
 *
 * Note that x_1,...,x_k are quantified in the left-hand side of the implication,
 * while the rest of the variables remain free to be quantified in the containing
 * induction case (see below). See for example @b TermAlgebra::getInductionTemplateTwo.
 */
struct InductionUnit
{
  InductionUnit(TermStack&& F_terms, LiteralStack&& conditions = LiteralStack(), VStack&& condUnivVars = VStack());

  void collectVariableSorts(const DHSet<unsigned>& sortVars, const TermStack& sorts, DHMap<unsigned,TermList>& varSorts) const;

  friend std::ostream& operator<<(std::ostream& out, const InductionUnit& u);

  TermStack F_terms;
  LiteralStack conditions;
  VStack condUnivVars;
};

/**
 * A formula template corresponding to a single case within an induction formula,
 * of the form ∀(∀ x_1,...,x_k.(U_1 ⋀ ... ⋀ U_m) → U), where
 * @b conclusion is the unit U,
 * @b hypotheses is the list of units U_1,...,U_n, and
 * @b hypUnivVars is the list of variables x_1,...,x_k.
 *
 * Note that x_1,...,x_k are quantified in the left-hand side of the implication,
 * and the rest of the free variables are universally quantified over the entire case.
 */
struct InductionCase
{
  InductionCase(InductionUnit&& conclusion, Stack<InductionUnit>&& hypotheses = Stack<InductionUnit>(), VStack&& hypUnivVars = VStack());

  friend std::ostream& operator<<(std::ostream& out, const InductionCase& c);

  InductionUnit conclusion;
  Stack<InductionUnit> hypotheses;
  VStack hypUnivVars;
};

/**
 * An induction formula template corresponding to ∀F(C_1 ⋀ ... ⋀ C_n → C),
 * where @b cases is the list C_1,...,C_n and @b conclusion is C.
 * The sorts of @b F_terms members must be equal to @b sorts and variables
 * not in @b sorts can only appear in at most one case or in the conclusion.
 *
 * See @b InductionClauseIterator::performInduction for the actual instantiation of the formula.
 */
struct InductionTemplate
{
  InductionTemplate(TermStack&& sorts, Stack<InductionCase>&& cases, InductionUnit&& conclusion, unsigned maxVar, InferenceRule rule);

  friend std::ostream& operator<<(std::ostream& out, const InductionTemplate& t);

  TermStack sorts;
  Stack<InductionCase> cases;
  InductionUnit conclusion;
  InferenceRule rule;
  unsigned maxVar;
};

}

#endif // __InductionTemplate__
