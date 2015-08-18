/**
 * @file Interpolants.hpp
 * Defines class Interpolants.
 */


#ifndef __Interpolants__
#define __Interpolants__

#include "Forwards.hpp"

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Term.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class Interpolants
{
public:
  Interpolants(DHSet<Unit*>* slicedOff=0) : _slicedOff(slicedOff) {}
  Formula* getInterpolant(Unit* refutation);
private:

  UnitIterator getParents(Unit* u);

  DHSet<Unit*>* _slicedOff;
};

};

#endif /* __Interpolants__ */
