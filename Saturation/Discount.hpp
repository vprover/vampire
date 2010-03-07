/**
 * @file Discount.hpp
 * Defines class Discount.
 */


#ifndef __Discount__
#define __Discount__

#include "../Forwards.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

class Discount
: public SaturationAlgorithm
{
public:
  Discount(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector)
    : SaturationAlgorithm(passiveContainer, selector) {}

  SaturationResult doSaturation();

  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();

};

};

#endif /* __Discount__ */
