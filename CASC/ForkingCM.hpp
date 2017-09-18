/**
 * @file ForkingCM.hpp
 * Defines class ForkingCM.
 */

#ifndef __ForkingCM__
#define __ForkingCM__

#include "Forwards.hpp"

#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"

#include "CASCMode.hpp"

namespace CASC
{

using namespace Lib;
using namespace Kernel;

class ForkingCM
: public CASCMode
{
public:
  ForkingCM();

protected:
  bool runSlice(Options& opt);
  void childRun(Options& opt) NO_RETURN;

private:
  ScopedPtr<Problem> _prb;
};

}

#endif // __ForkingCM__
