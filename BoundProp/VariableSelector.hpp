/**
 * @file BoundProp/VariableSelector.hpp
 * Defines class VariableSelector.
 */

#ifndef __VariableSelector__
#define __VariableSelector__
#if GNUMP
#include "Forwards.hpp"

namespace BoundProp {

using namespace Kernel;
using namespace Shell;

class VariableSelector {
protected:
  VariableSelector(Solver& solver);
public:
  virtual ~VariableSelector() {}
  /**
   * Return the next variable to be made into a decision point.
   *
   * When this function is called, there must be at least one
   * variable which does not have a tight bound.
   */
  virtual Var getNextVariable() = 0;

  static VariableSelector* create(Solver& s, Options& opt);
protected:
  bool isEligible(Var v);
  bool getNextEligibleVariable(Var firstPossible, Var& res);

  Solver& _solver;
  BoundsArray& _bounds;

  unsigned _varCnt;
};

}
#endif //GNUMP
#endif // __VariableSelector__
