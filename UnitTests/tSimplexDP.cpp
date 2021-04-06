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
#include "DP/SimplexDP.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Theory.hpp"

UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Inferences;

#include "Test/SyntaxSugar.hpp"

vector<DP::LinearArithmeticDP::Constraint> toConstraintsEqual(vector<vector<float>> c)
{
  vector<DP::LinearArithmeticDP::Constraint> constraints;
  for (unsigned i = 0; i < c.size(); i++) {
    DP::LinearArithmeticDP::Constraint constraint;
    constraint.predicate = Interpretation::RAT_LESS_EQUAL;

    for (unsigned j = 0; j < c[i].size() - 1; j++) {
      if (c[i][j] != 0) {
        constraint.parameters[j] = RationalConstantType(c[i][j]);
      }
    }
    constraint.constant = RationalConstantType(c[i][c[i].size() - 1]);
    constraints.push_back(constraint);
  }

  for (unsigned i = 0; i < c.size(); i++) {
    DP::LinearArithmeticDP::Constraint constraint;
    constraint.predicate = Interpretation::RAT_LESS_EQUAL;

    for (unsigned j = 0; j < c[i].size() - 1; j++) {
      if (c[i][j] != 0) {
        constraint.parameters[j] = -RationalConstantType(c[i][j]);
      }
    }
    constraint.constant = -RationalConstantType(c[i][c[i].size() - 1]);
    constraints.push_back(constraint);
  }

  return constraints;
}

vector<DP::LinearArithmeticDP::Constraint> toConstraintsLess(vector<vector<float>> c, bool equal)
{
  vector<DP::LinearArithmeticDP::Constraint> constraints;
  for (unsigned i = 0; i < c.size(); i++) {
    DP::LinearArithmeticDP::Constraint constraint;
    constraint.predicate = equal ? Interpretation::RAT_LESS_EQUAL : Interpretation::RAT_LESS;

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

vector<DP::LinearArithmeticDP::Constraint> toConstraintsGreater(vector<vector<float>> c, bool equal)
{
  vector<DP::LinearArithmeticDP::Constraint> constraints;
  for (unsigned i = 0; i < c.size(); i++) {
    DP::LinearArithmeticDP::Constraint constraint;
    constraint.predicate = equal ? Interpretation::RAT_LESS_EQUAL : Interpretation::RAT_LESS;

    for (unsigned j = 0; j < c[i].size() - 1; j++) {
      if (c[i][j] != 0) {
        constraint.parameters[j] = -RationalConstantType(c[i][j]);
      }
    }
    constraint.constant = -RationalConstantType(c[i][c[i].size() - 1]);
    constraints.push_back(constraint);
  }

  return constraints;
}

TEST_FUN(simplex1)
{
  vector<vector<float>> equalConstraintsVector = {
      {2, -1, 5, 10},
      {1, 1, -3, -2},
      {2, 4, 1, 1},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraintsEqual(equalConstraintsVector);

  DP::SimplexDP simplex = DP::SimplexDP(constraints);
  DP::DecisionProcedure::Status status = simplex.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);
}

TEST_FUN(simplex2)
{
  vector<vector<float>> equalConstraintsVector = {
      {-3, -5, 36, 10},
      {-1, 0, 7, 5},
      {1, 1, -10, -4},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraintsEqual(equalConstraintsVector);

  DP::SimplexDP simplex = DP::SimplexDP(constraints);
  DP::DecisionProcedure::Status status = simplex.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);
}

TEST_FUN(simplex3)
{
  vector<vector<float>> equalConstraintsVector = {
      {1, 1, 1, 3},
      {1, 1, 1, 4},
  };

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraintsEqual(equalConstraintsVector);

  DP::SimplexDP simplex = DP::SimplexDP(constraints);
  DP::DecisionProcedure::Status status = simplex.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::UNSATISFIABLE);
}

TEST_FUN(simplex4)
{
  vector<vector<float>> lessConstraintsVector = {
      {1, 3},
  };

  vector<vector<float>> greaterConstraintsVector = {
      {1, 3},
  };

  vector<DP::LinearArithmeticDP::Constraint> lessConstraints = toConstraintsLess(lessConstraintsVector, false);
  vector<DP::LinearArithmeticDP::Constraint> greaterConstraints = toConstraintsGreater(greaterConstraintsVector, false);

  vector<DP::LinearArithmeticDP::Constraint> constraints;
  constraints.insert(constraints.end(), lessConstraints.begin(), lessConstraints.end());
  constraints.insert(constraints.end(), greaterConstraints.begin(), greaterConstraints.end());

  DP::SimplexDP simplex = DP::SimplexDP(constraints);
  DP::DecisionProcedure::Status status = simplex.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::UNSATISFIABLE);
}

TEST_FUN(simplex5)
{
  vector<vector<float>> greaterEqualConstraintsVector = {
      {1, 1, 1},
      {1, -1, -1}};

  vector<DP::LinearArithmeticDP::Constraint> constraints = toConstraintsGreater(greaterEqualConstraintsVector, true);

  DP::SimplexDP simplex = DP::SimplexDP(constraints);
  DP::DecisionProcedure::Status status = simplex.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::SATISFIABLE);
}

TEST_FUN(simplex6)
{
  vector<vector<float>> lessEqualConstraintsVector = {
      {1, 1, 3}};

  vector<vector<float>> greaterEqaulConstraintsVector = {
      {1, 0, 2},
      {0, 1, 2}};

  vector<DP::LinearArithmeticDP::Constraint> lessEqualConstraints = toConstraintsLess(lessEqualConstraintsVector, false);
  vector<DP::LinearArithmeticDP::Constraint> greaterEqualConstraints = toConstraintsGreater(greaterEqaulConstraintsVector, false);

  vector<DP::LinearArithmeticDP::Constraint> constraints;
  constraints.insert(constraints.end(), lessEqualConstraints.begin(), lessEqualConstraints.end());
  constraints.insert(constraints.end(), greaterEqualConstraints.begin(), greaterEqualConstraints.end());

  DP::SimplexDP simplex = DP::SimplexDP(constraints);
  DP::DecisionProcedure::Status status = simplex.getStatus();
  ASS_EQ(status, DP::DecisionProcedure::UNSATISFIABLE);
}