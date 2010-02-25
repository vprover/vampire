/**
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"

#include "Otter.hpp"

namespace Saturation {

using namespace Kernel;

class LRS
: public Otter
{
public:
  LRS(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
  : Otter(passiveContainer,selector) {}

  //overrides Otter::saturate
  SaturationResult saturate();

protected:
  bool shouldUpdateLimits();

  long long estimatedReachableCount();

};

};

#endif /* __LRS__ */
