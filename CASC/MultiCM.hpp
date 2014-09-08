/**
 * @file MultiCM.hpp
 * Defines class MultiCM.
 */

#ifndef __MultiCM__
#define __MultiCM__

#include "Forwards.hpp"

#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"

#include "CASCMode.hpp"

namespace CASC
{

using namespace Lib;
using namespace Kernel;


class MultiCM
: public CASCMode
{
public:
  MultiCM(){};

protected:
  bool runSlice(Options& opt){ ASSERTION_VIOLATION; return false;};

private:
  ScopedPtr<Problem> _prb;
};

}

#endif // __MultiCM__
