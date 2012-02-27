/**
 * @file SimpleCongruenceClosure.hpp
 * Defines class SimpleCongruenceClosure.
 */

#ifndef __SimpleCongruenceClosure__
#define __SimpleCongruenceClosure__

#include "Forwards.hpp"

#include "DecisionProcedure.hpp"

namespace DP {

class SimpleCongruenceClosure : public DecisionProcedure {
  virtual void addLiterals(LiteralIterator lits) = 0;

  virtual Status getStatus() = 0;
  virtual void getUnsatisfiableSubset(LiteralStack& res) = 0;


};

}

#endif // __SimpleCongruenceClosure__
