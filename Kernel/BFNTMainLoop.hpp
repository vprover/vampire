/**
 * @file BFNTMainLoop.hpp
 * Defines class BFNTMainLoop.
 */

#ifndef __BFNTMainLoop__
#define __BFNTMainLoop__

#include "Forwards.hpp"

#include "Lib/SmartPtr.hpp"

#include "Shell/BFNT.hpp"

#include "MainLoop.hpp"

namespace Kernel {

using namespace Lib;
using namespace Shell;

class BFNTMainLoop : public MainLoop {
public:

  BFNTMainLoop(MainLoopSP inner) : _inner(inner) {}

  virtual void addInputClauses(ClauseIterator cit);

protected:
  virtual MainLoopResult runImpl();

private:

  void runChild(size_t modelSize) __attribute__((noreturn));
  MainLoopResult spawnChild(size_t modelSize);


  MainLoopSP _inner;

  BFNT _bfnt;
};

}

#endif // __BFNTMainLoop__
