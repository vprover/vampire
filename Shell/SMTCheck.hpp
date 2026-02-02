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
 * @file SMTCheck.hpp
 * Routines for producing a ground SMT proof-check script
 */

#include <iosfwd>

#include "Forwards.hpp"
#include "Shell/InferenceReplay.hpp"

namespace Shell {
namespace SMTCheck {

extern InferenceReplayer* replayer;

void outputSignature(std::ostream &out);
void outputStep(std::ostream &out, Kernel::Unit *u);

}
}
