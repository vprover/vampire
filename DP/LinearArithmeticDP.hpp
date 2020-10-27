
/*
 * File LinearArithmeticDP.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file LinearArithmeticDP.hpp
 * Defines class LinearArithmeticDP for implementing congruence closure
 */

#ifndef __LinearArithmeticDP__
#define __LinearArithmeticDP__

#include "Forwards.hpp"

#include "Lib/DArray.hpp"
#include "Lib/Deque.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Term.hpp"
#include "Kernel/Ordering.hpp"

#include "DecisionProcedure.hpp"

namespace DP {

using namespace Lib;
using namespace Kernel;

/**
 * General class for DPs for linear arithmetic
 * This class extracts a LA problem from the literals and then passes it elsewhere
 * to be solved. 
 */
class LinearArithmeticDP : public DecisionProcedure
{
public:
  CLASS_NAME(LinearArithmeticDP);
  USE_ALLOCATOR(LinearArithmeticDP);

  // TODO: Do we need to pass in anything?
  LinearArithmeticDP();

  virtual void addLiterals(LiteralIterator lits, bool onlyEqualites) override;
  void addLiteral(Literal* lit);

  virtual Status getStatus(bool retrieveMultipleCores) override;

  // TODO: For now we don't support unsat cores but we should do later
  virtual unsigned getUnsatCoreCount() override { return 0; } 
  virtual void getUnsatCore(LiteralStack& res, unsigned coreIndex) override {};

  // TODO: For now do nothing but consider if we want/need to support this later
  void getModel(LiteralStack& model) override {};
  
  virtual void reset() override;

private:

};

}

#endif // __LinearArithmeticDP__
