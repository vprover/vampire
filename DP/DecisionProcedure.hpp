/**
 * @file DecisionProcedure.hpp
 * Defines class DecisionProcedure.
 */

#ifndef __DecisionProcedure__
#define __DecisionProcedure__

#include "Forwards.hpp"

#include "Kernel/Term.hpp"



namespace DP {

using namespace Lib;
using namespace Kernel;

class DecisionProcedure {
public:
  enum Status {
    SATISFIABLE,
    UNSATISFIABLE,
    /**
     * When the decision procedure cannot determine
     * the satisfiability status of the literal set
     */
    UNKNOWN
  };

  virtual ~DecisionProcedure() {}

  virtual void addLiterals(LiteralIterator lits) = 0;

  virtual Status getStatus(bool getMultipleCores=false) = 0;

  /**
   * Return number of unsatisfiable cores that can be retrieved.
   * 0 is returned if the status is SATISFIABLE or UNKNOWN. If UNSATISFIABLE,
   * number greater than zero is returned.
   *
   * Can be called only after getStatus before any next call to addLiterals.
   */
  virtual unsigned getUnsatCoreCount() = 0;
  virtual void getUnsatCore(LiteralStack& res, unsigned coreIndex=0) = 0;

  /** reset decision procedure object into state equivalent to its initial state */
  virtual void reset() = 0;
};

class ScopedDecisionProcedure : public DecisionProcedure {
public:
  virtual void push() = 0;
  virtual void pop(unsigned scopeCount) = 0;
};

}

#endif // __DecisionProcedure__
