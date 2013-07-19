/*
 * MinimizeInvariants.hpp
 *
 *  Created on: Jun 10, 2013
 *      Author: ioan
 */
#if IS_LINGVA
#ifndef __MINIMIZEINVARIANTS_HPP__
#define __MINIMIZEINVARIANTS_HPP__

#include "Forwards.hpp"
#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"
#include "Shell/Property.hpp"

#include "Kernel/Problem.hpp"

#include <string>

#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

namespace Program{
using namespace Kernel;
using namespace Lib;

class MinimizeInvariants{
  public:
    virtual ~MinimizeInvariants(){}
    /**
     * Run the program analysis (lingva), generate the set of invariants
     * from the C-code, after that start consequence elimination strategies
     * on the set of invariants.
     * */
    static void run();

  protected:
    virtual bool runSlice(Options& opt) = 0;
    void handleSIGINT() __attribute__((noreturn));
  private:
    void perform();


  };

};//end namespace Program
#endif /* __MINIMIZEINVARIANTS_HPP__ */
#endif
