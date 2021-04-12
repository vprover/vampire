/*
 * File Simplex.hpp.
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
 * @file Simplex.hpp
 */

#ifndef __Simplex__
#define __Simplex__

#include "Forwards.hpp"
#include "DP/LinearArithmeticDP.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

namespace DP {
using namespace Lib;
using namespace Kernel;

class Simplex {
public:
  CLASS_NAME(Simplex);
  USE_ALLOCATOR(Simplex);

  Simplex(LinearArithmeticDP::Constraint objectiveFunc, vector<LinearArithmeticDP::Constraint> constraints, set<unsigned> colLabelSet);

  ~Simplex();

  enum Status {
    Unbounded,
    Optimal,
    Undefined
  };

  Status getStatus();
  RationalConstantType getOptimalValue();
  map<unsigned, RationalConstantType> getModel();
  RationalConstantType getModel(unsigned varId);

  unsigned getRowCount();

private:
  RationalConstantType **_tableau;
  unsigned _rowCount;
  unsigned _colCount;
  map<unsigned, unsigned> _colLabelMap;
  Status _status;

  void solve();
  bool canImprove();
  void pivotAbout(unsigned pivotRow, unsigned pivotCol);
};

} // namespace DP

#endif // __GaussElimination__
