
/*
 * File BFNTMainLoop.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file BFNTMainLoop.hpp
 * Defines class BFNTMainLoop.
 */

#ifndef __BFNTMainLoop__
#define __BFNTMainLoop__

#include "Lib/Portability.hpp"

#include "Forwards.hpp"

#include "Lib/SmartPtr.hpp"

#include "Kernel/MainLoop.hpp"

#include "BFNT.hpp"
#include "Options.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class BFNTMainLoop : public MainLoop {
public:
  CLASS_NAME(BFNTMainLoop);
  USE_ALLOCATOR(BFNTMainLoop);     
  
  BFNTMainLoop(Problem& prb, const Options& opt);

protected:
  virtual void init();
  virtual MainLoopResult runImpl();

private:

  /** If problem has sorts, we set this to true and just terminate with unknown
   * (at least until we have proper handling of sorts in BFNT) */
  bool _hasSorts;

  void runChild(size_t modelSize) __attribute__((noreturn));
  MainLoopResult spawnChild(size_t modelSize);

  Options _childOpts;
  /** the input transformer */
  BFNT _bfnt;
};

}

#endif // __BFNTMainLoop__
