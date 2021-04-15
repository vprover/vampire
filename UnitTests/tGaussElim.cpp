/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "DP/LinearArithmeticDP.hpp"
#include "DP/GaussElimination.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"

UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Inferences;

#include "Test/SyntaxSugar.hpp"

vector<DP::LinearArithmeticDP::Constraint> toConstraints(vector<vector<float>> c)
{
  vector<DP::LinearArithmeticDP::Constraint> constraints;
  for (unsigned i = 0; i < c.size(); i++) {
    DP::LinearArithmeticDP::Constraint constraint;
    constraint.predicate = Interpretation::EQUAL;

    for (unsigned j = 0; j < c[i].size() - 1; j++) {
      if (c[i][j] != 0) {
        constraint.parameters[j] = RationalConstantType(c[i][j]);
      }
    }
    constraint.constant = RationalConstantType(c[i][c[i].size() - 1]);
    constraints.push_back(constraint);
  }
  return constraints;
}

TEST_FUN(gauss_unique_solution1)
{
  vector<vector<float>> constraintsVector = {
      {2, -1, 5, 10},
      {1, 1, -3, -2},
      {2, 4, 1, 1},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraints(constraintsVector);

  DP::GaussElimination gauss = DP::GaussElimination(constraints);
  DP::DecisionProcedure::Status status = gauss.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);

  unsigned unsatCoreCount = gauss.getUnsatCoreCount();
  ASS_EQ(unsatCoreCount, 0);
}

TEST_FUN(gauss_unique_solution2)
{
  vector<vector<float>> constraintsVector = {
      {1, 1, 1, 5},
      {2, 3, 5, 8},
      {4, 0, 5, 2},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraints(constraintsVector);

  DP::GaussElimination gauss = DP::GaussElimination(constraints);
  DP::DecisionProcedure::Status status = gauss.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);

  unsigned unsatCoreCount = gauss.getUnsatCoreCount();
  ASS_EQ(unsatCoreCount, 0);
}

TEST_FUN(gauss_infinite_solutions1)
{
  vector<vector<float>> constraintsVector = {
      {-3, -5, 36, 10},
      {-1, 0, 7, 5},
      {1, 1, -10, -4},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraints(constraintsVector);

  DP::GaussElimination gauss = DP::GaussElimination(constraints);
  DP::DecisionProcedure::Status status = gauss.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);

  unsigned unsatCoreCount = gauss.getUnsatCoreCount();
  ASS_EQ(unsatCoreCount, 0);
}

TEST_FUN(gauss_infinite_solutions2)
{
  vector<vector<float>> constraintsVector = {
      {1, 1, 2, 1},
      {2, -1, 1, 2},
      {4, 1, 5, 4},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraints(constraintsVector);

  DP::GaussElimination gauss = DP::GaussElimination(constraints);
  DP::DecisionProcedure::Status status = gauss.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);

  unsigned unsatCoreCount = gauss.getUnsatCoreCount();
  ASS_EQ(unsatCoreCount, 0);
}

TEST_FUN(gauss_no_solution1)
{
  vector<vector<float>> constraintsVector = {
      {1, 1, 1, 3},
      {1, 1, 1, 4},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraints(constraintsVector);

  DP::GaussElimination gauss = DP::GaussElimination(constraints);
  DP::DecisionProcedure::Status status = gauss.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::UNSATISFIABLE);

  unsigned unsatCoreCount = gauss.getUnsatCoreCount();
  ASS(unsatCoreCount > 0);
}

TEST_FUN(gauss_no_solution2)
{
  vector<vector<float>> constraintsVector = {
      {1, 1, 3},
      {1, 2, 7},
      {4, 6, 21}};

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraints(constraintsVector);

  DP::GaussElimination gauss = DP::GaussElimination(constraints);
  DP::DecisionProcedure::Status status = gauss.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::UNSATISFIABLE);

  unsigned unsatCoreCount = gauss.getUnsatCoreCount();
  ASS(unsatCoreCount > 0);
}