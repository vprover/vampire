/**
 * @file ForkingSM
 * Defines class ForkingSM
 */

#ifndef __ForkingSM__
#define __ForkingSM__

#include "Forwards.hpp"

#include "Lib/Portability.hpp"
#include "Lib/ScopedPtr.hpp"

#include "Kernel/Problem.hpp"

#include "SMTCOMPMode.hpp"

namespace SMTCOMP
{

using namespace Lib;
using namespace Kernel;

#if COMPILER_MSVC

class ForkingSM
: public SMTCOMPMode
{
  ForkingSM() { INVALID_OPERATION("Forking SMTCOMP mode is not supported on the Windows platform."); }
  bool runSlice(Options& opt) { ASSERTION_VIOLATION; }
};

#else

class ForkingSM
: public SMTCOMPMode
{
public:
  ForkingSM();

protected:
  bool runSlice(Options& opt);
  void childRun(Options& opt) NO_RETURN;

private:
  ScopedPtr<Problem> _prb;
};

#endif

}

#endif // __ForkingSM__
