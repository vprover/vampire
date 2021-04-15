/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __SHELL__UNIFICATION_WITH_ABSTRACTION_CONFIG__
#define __SHELL__UNIFICATION_WITH_ABSTRACTION_CONFIG__

#include "Kernel/Term.hpp"

namespace Shell {


class UnificationWithAbstractionConfig 
{
public:
  UnificationWithAbstractionConfig()  {}

  static bool isInterpreted(Kernel::Term* t   );
  static bool isInterpreted(Kernel::TermList t);
};

} // namespace Shell

#endif // __SHELL__UNIFICATION_WITH_ABSTRACTION_CONFIG__
