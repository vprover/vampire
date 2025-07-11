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
 *  @file Interface.hpp
 *  Defines class Interface
 *  @since 10/07/2025
 */

#ifndef __Interface__
#define __Interface__

#include <string>
#include <vector>

namespace Interactive {

void init(); // please call this at the start

bool loadTPTP(std::string tag, std::string theory); // returns true on success; state should remain consistent anyway

std::vector<std::string> listTheories();

bool popTeories(unsigned popCnt); // will try to pop popCnt many theories from the theory stack; returns true if there were enough theories on the stack to pop, even in the false case theories will be popped



}

#endif /* __Interface__ */
