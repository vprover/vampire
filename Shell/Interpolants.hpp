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
 * @file Interpolants.hpp
 * Defines class Interpolants.
 */


#ifndef __Interpolants__
#define __Interpolants__

#include "Forwards.hpp"

namespace Shell {

class Interpolants
{
public:
  static void removeConjectureNodesFromRefutation(Kernel::Unit* refutation);
  static Unit* formulifyRefutation(Kernel::Unit* refutation);
};

};

#endif /* __Interpolants__ */
