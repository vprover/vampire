/**
 * @file SubsumptionRemover.hpp
 * Defines class SubsumptionRemover.
 */

#ifndef __SubsumptionRemover__
#define __SubsumptionRemover__
#if GNUMP
#include "Forwards.hpp"

namespace Shell {

using namespace Lib;
using namespace Kernel;

class SubsumptionRemover {
public:
  bool apply(ConstraintRCList*& lst);
private:
  struct CoeffArrayHash;

  bool firstIsSubsumed(Constraint& c1, Constraint& c2);
};

}

#endif //GNUMP
#endif // __SubsumptionRemover__
