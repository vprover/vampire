/**
 * @file BoundPropagator.hpp
 * Defines class BoundPropagator.
 */

#ifndef __BoundPropagator__
#define __BoundPropagator__
#if GNUMP
#include <utility>

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/V2CIndex.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"
#include "BoundsArray.hpp"

namespace BoundProp {

using namespace std;
using namespace Shell;

class BoundPropagator {
private:
  BoundPropagator(Solver& solver, Options& opt);

public:
  virtual ~BoundPropagator() {}

  BoundSuggestionResult propagate();

  BoundSuggestionResult propagateDecisionPoints();

  BoundSuggestionResult propagateBounds(Constraint& constr, bool tightBoundsOnly=false);
  BoundSuggestionResult propagateBounds(Constraint& constr, Var v);

  void registerConstraint(Constraint* constr);

  static BoundPropagator* create(Solver& s, Options& opt);
private:
  /** Identifies a bound of a variable. The second member is true if the bound is left. */
  typedef Stack<BoundId> BoundIdStack;

  class BoundConstraintIteratorFn;

  void collectUpdated(BoundsArray::UpdateQueue& que, BoundIdStack& updSet, bool tightBoundsOnly=false);

  Solver& _solver;
  BoundsArray& _bounds;
  bool _useCollapsingConstraints;
  unsigned _updatesByOneConstraint;

  unsigned _varCnt;

  /**
   * Constraints grouped by bounds that can be propagated through them
   */
  V2CIndex _constrByBound;
};

}
#endif //GNUMP
#endif // __BoundPropagator__
