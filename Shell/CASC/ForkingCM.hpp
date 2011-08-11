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

namespace Shell
{
namespace CASC
{

using namespace Lib;
using namespace Kernel;

#if COMPILER_MSVC

class ForkingCM
: public CASCMode
{
  ForkingCM() { INVALID_OPERATION("Forking CASC mode is not supported on the Windows platform."); }
  bool runSlice(Options& opt) { ASSERTION_VIOLATION; }
};

#else

class ForkingCM
: public CASCMode
{
public:
  ForkingCM();

protected:
  bool runSlice(Options& opt);
  void childRun(Options& opt) __attribute__((noreturn));

private:
  ScopedPtr<Problem> _prb;
};

#endif

}
}

#endif // __ForkingCM__
