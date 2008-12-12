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
  Discount(PassiveClauseContainer* passiveContainer, LiteralSelector* selector)
    : SaturationAlgorithm(passiveContainer,selector) {}
  SaturationResult saturate();

  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();

protected:
  bool processInactive(Clause* c);
  void activate(Clause* c);
};

};

#endif /* __Discount__ */
