/**
 * @file BDDMarkingSubsumption.hpp
 * Defines class BDDMarkingSubsumption.
 */

#ifndef __BDDMarkingSubsumption__
#define __BDDMarkingSubsumption__

#include "../Forwards.hpp"

namespace Inferences {

using namespace Kernel;
using namespace Saturation;

class BDDMarkingSubsumption {
public:
  void init(SaturationAlgorithm* sa);

  void onAllProcessed();
  void onNewPropositionalClause(Clause* cl);

  bool subsumed(Clause* cl);

private:
  SaturationAlgorithm* _sa;
};

}

#endif // __BDDMarkingSubsumption__
