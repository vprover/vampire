/**
 * @file Discount.hpp
 * Defines class Discount.
 */


#ifndef __Discount__
#define __Discount__

#include "Saturation/SaturationAlgorithm.hpp"

namespace Kernel{
	class Problem;
}

namespace Shell{
	class Options;
}

namespace Saturation {

class Discount: public SaturationAlgorithm {

public:
  CLASS_NAME(Discount);
  USE_ALLOCATOR(Discount);

  Discount(Kernel::Problem& prb, const Shell::Options& opt): SaturationAlgorithm(prb, opt) {}

  Kernel::ClauseContainer* getSimplifyingClauseContainer();

protected:

  //overrides SaturationAlgorithm::handleClauseBeforeActivation
  bool handleClauseBeforeActivation(Kernel::Clause* cl);

};

}

#endif /* __Discount__ */
