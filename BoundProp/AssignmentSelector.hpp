/**
 * @file AssignmentSelector.hpp
 * Defines class AssignmentSelector.
 */

#ifndef __AssignmentSelector__
#define __AssignmentSelector__
#if GNUMP

#include "Forwards.hpp"

namespace BoundProp {

using namespace Kernel;
using namespace Shell;

class AssignmentSelector {
public:
  virtual ~AssignmentSelector() {}
  virtual void getAssignment(Var var, BoundNumber& result) = 0;

  static AssignmentSelector* create(Solver& s, Options& opt);
};

}
#endif //GNUMP
#endif // __AssignmentSelector__
