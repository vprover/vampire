/**
 * @file ForkingCM.hpp
 * Defines class ForkingCM.
 */

#ifndef __ForkingCM__
#define __ForkingCM__

#include "Forwards.hpp"

#include "Lib/Portability.hpp"

#include "Shell/Property.hpp"

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

  Property* getProperty() { ASSERTION_VIOLATION; }

  bool runStrategy(string strategy, unsigned ds) { ASSERTION_VIOLATION; }
};

#else

class ForkingCM
: public CASCMode
{
public:
  ForkingCM();

protected:
  Property* getProperty() { return &_property; }

  bool runStrategy(string strategy, unsigned ds);

  void childRun(string strategy, unsigned ds) __attribute__((noreturn));

private:
  UnitList* _units;
  Property _property;
};

#endif

}
}

#endif // __ForkingCM__
