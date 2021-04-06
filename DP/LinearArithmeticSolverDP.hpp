#ifndef __LinearArithmeticSolverDP__
#define __LinearArithmeticSolverDP__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"

#include "DP/DecisionProcedure.hpp"

namespace DP {

using namespace Lib;
using namespace Kernel;

/**
 * A pure virtual class implementing Linear decision procedures.
 */
class LinearArithmeticSolverDP {
public:
  virtual ~LinearArithmeticSolverDP() {}

  /** return the result */
  virtual DecisionProcedure::Status getStatus() = 0;

  virtual map<unsigned, RationalConstantType> getModel() = 0;

  /**
   * Return number of unsatisfiable cores that can be retrieved.
   * 0 is returned if the status is SATISFIABLE or UNKNOWN. If UNSATISFIABLE,
   * number greater than zero is returned.
   *
   * Can be called only after getStatus before any next call to addLiterals.
   */
  virtual unsigned getUnsatCoreCount() = 0;
  virtual set<unsigned>  getUnsatCore(unsigned coreIndex) = 0;
  /** reset decision procedure object into state equivalent to its initial state */
};

} // namespace DP

#endif // __LinearArithmeticSolverDP__
