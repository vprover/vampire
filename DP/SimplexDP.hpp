/*
 * File SimplexDP.hpp.
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
 * @file SimplexDP.hpp
 */

#ifndef __SimplexDP__
#define __SimplexDP__

#include <vector>
#include <set>
#include "Forwards.hpp"
#include "Lib/List.hpp"
#include "LinearArithmeticDP.hpp"
#include "DecisionProcedure.hpp"
#include "LinearArithmeticSolverDP.hpp"
#include "DP/Simplex.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

namespace DP {
using namespace Lib;
using namespace Kernel;

class SimplexDP : public LinearArithmeticSolverDP {
public:
  CLASS_NAME(SimplexDP);
  USE_ALLOCATOR(SimplexDP);

  SimplexDP(vector<LinearArithmeticDP::Constraint> &constraints);
  ~SimplexDP();

  virtual LinearArithmeticDP::Status getStatus() override;
  virtual vector<Literal *> getModel() override;
  virtual unsigned getUnsatCoreCount() override;
  virtual set<unsigned> getUnsatCore(unsigned coreIndex) override;

private:
  Simplex *_simplexSolver;
  
  unsigned *_alphaVarId;
  RationalConstantType _satOptimalValue;
  LinearArithmeticDP::Status _status;

  void solve();
};

} // namespace DP

#endif // __SimplexDP__
