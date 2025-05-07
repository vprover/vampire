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

/**
 * Similar to a second-order formula that we use for induction,
 * with one universally-quantified second-order variable.
 */
struct InductionTemplate
{
  InductionTemplate(InferenceRule rule) : rule(rule) {}
  struct Case {
    Case(Stack<TermStack>&& hyps, TermStack&& main)
      : hyps(hyps), main(main) {}

    Stack<TermStack> hyps;
    TermStack main;
  };
  Stack<Case> cases;
  InferenceRule rule;
};

}

#endif // __InductionTemplate__
