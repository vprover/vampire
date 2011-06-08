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
  typedef InferenceStore::UnitSpec UnitSpec;

  Interpolants(DHSet<UnitSpec>* slicedOff=0) : _slicedOff(slicedOff) {}
  Formula* getInterpolant(Clause* refutation);
private:

  VirtualIterator<UnitSpec> getParents(UnitSpec u);

  DHSet<UnitSpec>* _slicedOff;
};

};

#endif /* __Interpolants__ */
