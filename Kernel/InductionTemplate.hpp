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

namespace Kernel {

/**
 * Similar to a second-order formula that we use for induction,
 * with one universally-quantified second-order variable.
 */
struct InductionTemplate
{
  struct Case {
    Case(Stack<TermStack>&& hyps, TermStack&& main)
      : _hyps(hyps), _main(main) {}

    Stack<TermStack> _hyps;
    TermStack _main;
  };
  Stack<Case> _cases;
};

}

#endif // __InductionTemplate__
