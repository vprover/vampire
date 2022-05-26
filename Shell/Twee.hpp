/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __Twee__
#define __Twee__

#include "Forwards.hpp"

namespace Shell {

class Twee {
public:
  void apply(Kernel::Problem &);

private:
  bool handleTerm(Kernel::Problem &, Kernel::TermList t);
  DHSet<Kernel::Term *> _seen;
};

};

#endif /* __Twee__ */
