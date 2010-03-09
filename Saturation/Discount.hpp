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

  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();

protected:

  //overrides SaturationAlgorithm::handleClauseBeforeActivation
  bool handleClauseBeforeActivation(Clause* cl);

};

};

#endif /* __Discount__ */
