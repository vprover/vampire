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
    UNSATISFIABLE
  };

  virtual ~DecisionProcedure() {}

  virtual void addLiterals(LiteralIterator lits) = 0;

  virtual Status getStatus() = 0;
  virtual void getUnsatisfiableSubset(LiteralStack& res) = 0;
};

class ScopedDecisionProcedure : public DecisionProcedure {
public:
  virtual void push() = 0;
  virtual void pop(unsigned scopeCount) = 0;
};

}

#endif // __DecisionProcedure__
