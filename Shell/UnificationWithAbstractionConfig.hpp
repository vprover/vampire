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
