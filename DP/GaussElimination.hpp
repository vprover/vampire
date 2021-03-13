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
#include "Forwards.hpp"
#include "Lib/List.hpp"
#include "LinearArithmeticDP.hpp"
#include "DecisionProcedure.hpp"
#include "LinearArithmeticSolverDP.hpp"

#include "Lib/Environment.hpp"
#include "Kernel/Signature.hpp"

namespace DP {
using namespace Lib;
using namespace Kernel;

class GaussElimination : public LinearArithmeticSolverDP {
public:
  CLASS_NAME(GaussElimination);
  USE_ALLOCATOR(GaussElimination);

  GaussElimination(std::vector<List<LinearArithmeticDP::Parameter> *> rowsVector, std::set<unsigned int> colLabelSet);
  ~GaussElimination();

  virtual LinearArithmeticDP::Status getStatus() override;

  virtual void getModel(LiteralStack& model) override;

private:
  List<LinearArithmeticDP::Parameter> **rowsList;
  unsigned int *colLabelList;
  unsigned int numberOfUnkowns;
  unsigned int numberOfRows;
  float *solutions;

  float getCoefficient(List<LinearArithmeticDP::Parameter> *row, unsigned int varId);
  List<LinearArithmeticDP::Parameter> *subtract(List<LinearArithmeticDP::Parameter> *e1, List<LinearArithmeticDP::Parameter> *e2, float multiplier);
  int getColLabelIndex(unsigned int label, unsigned int searchStartIndex);
};

} // namespace DP

#endif // __GaussElimination__
