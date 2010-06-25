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
  void registerForkHandlers(VoidFunc before, VoidFunc afterParent, VoidFunc afterChild);
private:
  Multiprocessing();
  ~Multiprocessing();

  static void executeFuncList(VoidFuncList* lst);

  VoidFuncList* _preFork;
  VoidFuncList* _postForkParent;
  VoidFuncList* _postForkChild;
};

}
}

#endif // __Multiprocessing__
