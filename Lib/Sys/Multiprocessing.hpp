/**
 * @file Multiprocessing.hpp
 * Defines class Multiprocessing.
 */

#ifndef __Multiprocessing__
#define __Multiprocessing__

#include "Forwards.hpp"
#include <unistd.h>

namespace Lib {
namespace Sys {

class Multiprocessing {
public:
  static Multiprocessing* instance();

  pid_t waitForChildTermination(int& resValue);
  pid_t waitForChildTerminationOrTime(unsigned timeMs,int& resValue);
  void waitForParticularChildTermination(pid_t child, int& resValue);

  pid_t fork();
  void registerForkHandlers(VoidFunc before, VoidFunc afterParent, VoidFunc afterChild);

  void sleep(unsigned ms);
  void kill(pid_t child, int signal);
  void killNoCheck(pid_t child, int signal);
  pid_t poll_children(bool &stopped, bool &exited, bool &signalled, int &code);
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
