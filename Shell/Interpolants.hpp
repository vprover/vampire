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
  struct ItemState;

  void generateInterpolant(ItemState& st);

  UnitIterator getParents(Unit* u);

  DHSet<Unit*>* _slicedOff;

  DHMap<SplitLevel,Clause*> _splittingComponents;
};

};

#endif /* __Interpolants__ */
