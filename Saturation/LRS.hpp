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


protected:

  //overrides Otter::doSaturation
  SaturationResult doSaturation();

  //overrides SaturationAlgorithm::onUnprocessedSelected
  void onUnprocessedSelected(Clause* c);

  bool shouldUpdateLimits();

  long long estimatedReachableCount();

  bool _complete;
};

};

#endif /* __LRS__ */
