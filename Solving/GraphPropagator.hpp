/**
 * @file GraphPropagator.hpp
 * Defines class GraphPropagator.
 */

#ifndef __GraphPropagator__
#define __GraphPropagator__
#if GNUMP
#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Number.hpp"

namespace Solving {

using namespace Lib;
using namespace Kernel;

class GraphPropagator {
  class CPropagationInfo {
    /**
     * i-th element contains value of bound inferred by the
     * constraint for the i-th variable in the constraint.
     */
    DArray<BoundNumber> _vals;
    /**
     * i-th element contains true if the bound inferred by the
     * constraint for the i-th variable was strict.
     */
    DArray<bool> _strict;
    DecisionLevel _depth;
    unsigned unboundCnt;
    bool _constrStrict;

  };
  class CInfo {
    Stack<CPropagationInfo> _piStack;
  };

  //constraint number --> ConstrainInfo
  DHMap<unsigned, CInfo> _cinf;
};

}
#endif //GNUMP
#endif // __GraphPropagator__
