/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#ifndef __Shell_SimplificationReplay__
#define __Shell_SimplificationReplay__

#include "Forwards.hpp"

namespace Shell::SimplificationReplay {
/** Recover certificates directly from the recorded main and side parents.
 * These simplifications require search-time context that is absent from the
 * proof, or select a first candidate that may differ from the recorded goal. */
void literalRewriting(Kernel::Clause* main, Kernel::Clause* side);
void subsumptionResolution(Kernel::Clause* main, Kernel::Clause* side);
}

#endif
