/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

/* Isolated destructor probes for the unchanged upstream production code. */
#include <iostream>

#include "Test/UnitTesting.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/SATInference.hpp"
#include "SAT/SATLiteral.hpp"

TEST_FUN(destroy_sat_inference)
{
  SAT::SATLiteralStack literals;
  auto refutation = SAT::SATClause::fromStack(literals);
  refutation->setInference(new SAT::PropInference(static_cast<SAT::SATClauseList*>(nullptr)));
  Kernel::Inference inference(Kernel::InferenceOfASatClause(
      Kernel::InferenceRule::AVATAR_REFUTATION, refutation, nullptr));
  std::cout << "F08_BEGIN inference.destroy" << std::endl;
  inference.destroy();
  std::cout << "F08_END inference.destroy" << std::endl;
}

TEST_FUN(destroy_long_label_boolean_term_formula)
{
  Kernel::Formula* formula = new Kernel::BoolTermFormula(Kernel::TermList::var(0));
  formula->label("a formula label longer than the small string buffer");
  std::cout << "F12_BEGIN formula.destroy label_length=50" << std::endl;
  formula->destroy();
  std::cout << "F12_END formula.destroy" << std::endl;
}
