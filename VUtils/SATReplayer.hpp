
/*
 * File SATReplayer.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file SATReplayer.hpp
 * Defines class SATReplayer.
 */

#ifndef __SATReplayer__
#define __SATReplayer__

#include "Forwards.hpp"

namespace VUtils {

class SATReplayer {
public:
  int perform(int argc, char** argv);
};

}

#endif // __SATReplayer__
