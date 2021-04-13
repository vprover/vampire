/*
 * File GaussElimination.hpp.
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
 * @file GaussElimination.hpp
 */

#ifndef __GaussElimination__
#define __GaussElimination__

#include <vector>
#include <set>
#include "LinearArithmeticDP.hpp"
#include "DecisionProcedure.hpp"
#include "LinearArithmeticSolverDP.hpp"

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

namespace DP {
using namespace Lib;
using namespace Kernel;

class GaussElimination : public LinearArithmeticSolverDP {
public:
  CLASS_NAME(GaussElimination);
  USE_ALLOCATOR(GaussElimination);

  GaussElimination(vector<LinearArithmeticDP::Constraint> parsedLiterals);
  ~GaussElimination();

  enum Status {
    UNKNOWN,
    SATISFIABLE_ONE,
    SATISFIABLE_INFINITE,
    UNSATISFIABLE
  };

  virtual LinearArithmeticDP::Status getStatus() override;

  virtual vector<Literal *> getModel() override;

  virtual unsigned getUnsatCoreCount() override;
  virtual set<unsigned> getUnsatCore(unsigned coreIndex) override;

private:
  vector<LinearArithmeticDP::Constraint> _rowsList;
  set<unsigned> _colLabelSet;
  Status _status;
  vector<Literal *> _model;
  vector<unsigned> _inconsistentRowIndexes;
  vector<set<unsigned>> _unsatCores;

  void solve();
  void subtract(LinearArithmeticDP::Constraint *c1, LinearArithmeticDP::Constraint *c2, RationalConstantType multiplier);

  void setModel();

  void setUnsatCore();
  bool setInterference(LinearArithmeticDP::Constraint *row, set<unsigned> *interferenceSet);
  bool isInterfearing(LinearArithmeticDP::Constraint *row, set<unsigned> *interferenceSet);
  bool areInconsistentMultiples(LinearArithmeticDP::Constraint *row1, LinearArithmeticDP::Constraint *row2);
};

} // namespace DP

#endif // __GaussElimination__
