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
  struct Atom {
    Atom(TermStack&& F_terms, LiteralStack&& conditions = LiteralStack())
      : F_terms(F_terms), conditions(conditions) {}
    TermStack F_terms;
    LiteralStack conditions;
  };

  struct Case {
    Case(Stack<Atom>&& hypotheses, Atom&& conclusion)
      : hypotheses(hypotheses), conclusion(conclusion) {}

    Stack<Atom> hypotheses;
    Atom conclusion;
  };

  InductionTemplate(Stack<Case>&& cases, Atom&& conclusion, InferenceRule rule)
    : cases(cases), conclusion(conclusion), rule(rule)
  {
    //TODO add debug check for arities
  }

  Stack<Case> cases;
  Atom conclusion;
  InferenceRule rule;
};

}

#endif // __InductionTemplate__
