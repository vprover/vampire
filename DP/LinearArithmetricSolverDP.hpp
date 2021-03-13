#ifndef __LinearArithmeticSolverDP__
#define __LinearArithmeticSolverDP__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"

#include "DP/DecisionProcedure.hpp"

namespace DP {

using namespace Lib;
using namespace Kernel;

/**
 * A pure virtual class implementing decision procedures.
 */
class LinearArithmeticSolverDP {
public:
  virtual ~LinearArithmeticSolverDP() {}

  /** return the result */
  virtual DecisionProcedure::Status getStatus() = 0;

  // TODO: this is needed for the model experiment with the SimpleCongruenceClosure class
  // but does it make sense for a general dp?
  virtual void getModel(LiteralStack& model) = 0;

  /**
   * Return number of unsatisfiable cores that can be retrieved.
   * 0 is returned if the status is SATISFIABLE or UNKNOWN. If UNSATISFIABLE,
   * number greater than zero is returned.
   *
   * Can be called only after getStatus before any next call to addLiterals.
   */
  //virtual unsigned getUnsatCoreCount() = 0;
  //virtual void getUnsatCore(LiteralStack& res, unsigned coreIndex=0) = 0;
  /** reset decision procedure object into state equivalent to its initial state */
};

} // namespace DP

#endif // __LinearArithmeticSolverDP__
