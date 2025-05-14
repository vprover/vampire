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
 * @file Multiprocessing.hpp
 * Defines class Multiprocessing.
 */

#ifndef __Multiprocessing__
#define __Multiprocessing__

#include "Forwards.hpp"

namespace Lib {
namespace Sys {

class Multiprocessing {
public:
  static Multiprocessing* instance();

  pid_t waitForChildTermination(int& resValue);
  pid_t fork();

  void kill(pid_t child, int signal);
  void killNoCheck(pid_t child, int signal);
  pid_t poll_children(bool &exited, bool &signalled, int &code);
};

}
}

#endif // __Multiprocessing__
