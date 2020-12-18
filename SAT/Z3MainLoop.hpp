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
 * @file Z3MainLoop.hpp
 * Defines class Z3MainLoop.
 */

#ifndef __Z3MainLoop__
#define __Z3MainLoop__

#if VZ3

#include "Forwards.hpp"

#include "Lib/Allocator.hpp"

#include "Kernel/MainLoop.hpp"
#include "Kernel/Problem.hpp"

#include "SAT/Z3Interfacing.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

namespace SAT{

using namespace Kernel;
using namespace Shell;
using namespace Lib;

class Z3MainLoop : public MainLoop 
{
public:
  CLASS_NAME(Z3MainLoop);
  USE_ALLOCATOR(Z3MainLoop);  
  
  Z3MainLoop(Problem& prb, const Options& opt);
  ~Z3MainLoop(){};

protected:
  virtual void init();
  virtual MainLoopResult runImpl();
//private:

};

} // end SAT namespace

#endif // if VZ3
#endif // __Z3MainLoop__
