/**
 * @file Discount.hpp
 * Defines class Discount.
 */


#ifndef __Discount__
#define __Discount__

#include "Forwards.hpp"

#include "SaturationAlgorithm.hpp"

namespace Saturation {

using namespace Kernel;

class Discount
: public SaturationAlgorithm
{
public:
  Discount(PassiveClauseContainer* passiveContainer, LiteralSelector* selector)
    : SaturationAlgorithm(passiveContainer, selector) {}

  ClauseContainer* getSimplifyingClauseContainer();

protected:

  //overrides SaturationAlgorithm::handleClauseBeforeActivation
  bool handleClauseBeforeActivation(Clause* cl);

};

};

#endif /* __Discount__ */
