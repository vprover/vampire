/**
 * @file ConflictSelector.hpp
 * Defines class ConflictSelector.
 */

#ifndef __ConflictSelector__
#define __ConflictSelector__

#if GNUMP
#include "Forwards.hpp"

namespace Solving {

using namespace Lib;
using namespace Kernel;
using namespace Shell;

class ConflictSelector {
protected:
  ConflictSelector(Solver& s);
public:
  void getConflictIndexes(Var v, size_t& left, size_t& right);

  static ConflictSelector* create(Solver& s, Options& opt);
protected:
  virtual void getConflictIndexes(Var v, const BoundStack& leftBounds,
      const BoundStack& rightBounds, size_t& left, size_t& right) = 0;

  Solver& _solver;
  BoundsArray& _bounds;
};

}
#endif
#endif // __ConflictSelector__
