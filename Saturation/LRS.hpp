/**
 * @file LRS.hpp
 * Defines class LRS.
 */


#ifndef __LRS__
#define __LRS__

#include "Forwards.hpp"

#include "Lib/Event.hpp"

#include "Otter.hpp"

namespace Saturation {

using namespace Kernel;

class LRS
: public Otter
{
public:
  LRS(Problem& prb, const Options& opt)
  : Otter(prb, opt), _limitsEverActive(false) {}


protected:

  //overrides SaturationAlgorithm::isComplete
  bool isComplete();

  //overrides SaturationAlgorithm::onUnprocessedSelected
  void onUnprocessedSelected(Clause* c);

  bool shouldUpdateLimits();

  long long estimatedReachableCount();

  bool _limitsEverActive;
};

};

#endif /* __LRS__ */
