/**
 * @file Interpolants.hpp
 * Defines class Interpolants.
 */


#ifndef __Interpolants__
#define __Interpolants__

#include "Forwards.hpp"

#include "Kernel/Term.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class Interpolants
{
public:
  static Formula* getInterpolant(Clause* refutation);
private:
};

};

#endif /* __Interpolants__ */
