/*
 * File SimplexDP.cpp.
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
 * @file SimplexDP.cpp
 * Implements class Simplex decision procedure.
 */
#define SMDP DLADP

#include "SimplexDP.hpp"

#include "Lib/List.hpp"
#include "Kernel/Sorts.hpp"

#include <iostream>
#include <vector>
#include <iterator>
#include <set>
#include <typeinfo>

namespace DP {

SimplexDP::SimplexDP(vector<LinearArithmeticDP::Constraint> constraints)
{
  CALL("SimplexDP::SimplexDP");

  // Seperating constraints into D1 and D2 and for each variable replace with two non-negative variable x => x1 - x2
  std::vector<LinearArithmeticDP::Constraint> d1ParameterDataContainer;
  std::vector<LinearArithmeticDP::Constraint> d2ParameterDataContainer;

  std::set<unsigned> newColLabelSet;
  for (unsigned i = 0; i < constraints.size(); i++) {
    LinearArithmeticDP::Constraint currentParameterDataContainer = constraints[i];

    RationalConstantType rhsConstant = currentParameterDataContainer.constant;
    if (rhsConstant.isPositive() || rhsConstant.isZero()) {
      // D1
      LinearArithmeticDP::Constraint newParameterDataContainer;
      newParameterDataContainer.constant = currentParameterDataContainer.constant;
      newParameterDataContainer.predicate = currentParameterDataContainer.predicate;

      map<unsigned, RationalConstantType>::iterator it = currentParameterDataContainer.parameters.begin();
      while (it != currentParameterDataContainer.parameters.end()) {
        RationalConstantType parameterCoefficient = it->second;
        newParameterDataContainer.parameters[it->first * 2] = parameterCoefficient;
        newParameterDataContainer.parameters[(it->first * 2) + 1] = -parameterCoefficient;
        newColLabelSet.insert(it->first * 2);
        newColLabelSet.insert((it->first * 2) + 1);
        it++;
      }
      d1ParameterDataContainer.push_back(newParameterDataContainer);
    }
    else {
      // D2
      LinearArithmeticDP::Constraint newParameterDataContainer;
      newParameterDataContainer.constant = -currentParameterDataContainer.constant;
      newParameterDataContainer.predicate = currentParameterDataContainer.predicate;

      map<unsigned, RationalConstantType>::iterator it = currentParameterDataContainer.parameters.begin();
      while (it != currentParameterDataContainer.parameters.end()) {
        RationalConstantType parameterCoefficient = it->second;
        newParameterDataContainer.parameters[it->first * 2] = -parameterCoefficient;
        newParameterDataContainer.parameters[(it->first * 2) + 1] = parameterCoefficient;
        newColLabelSet.insert(it->first * 2);
        newColLabelSet.insert((it->first * 2) + 1);
        it++;
      }
      d2ParameterDataContainer.push_back(newParameterDataContainer);
    }
  }

  unsigned lastParameterId = *newColLabelSet.rbegin();
  _alphaVarId = lastParameterId + 1 + d2ParameterDataContainer.size();
#if SMDP
  cout << "alphaVarId: " << _alphaVarId << endl;
#endif

  // Add alpha to d1
  for (unsigned i = 0; i < d1ParameterDataContainer.size(); i++) {
    if (d1ParameterDataContainer[i].predicate == Interpretation::RAT_LESS) {
      d1ParameterDataContainer[i].parameters[_alphaVarId] = RationalConstantType(1);
      newColLabelSet.insert(_alphaVarId);
    }
  }

  // Add z and alpha to d2
  for (unsigned i = 0; i < d2ParameterDataContainer.size(); i++) {
    d2ParameterDataContainer[i].parameters[(lastParameterId + 1) + i] = RationalConstantType(-1);
    newColLabelSet.insert((lastParameterId + 1) + i);

    if (d2ParameterDataContainer[i].predicate == Interpretation::RAT_LESS) {
      d2ParameterDataContainer[i].parameters[_alphaVarId] = RationalConstantType(-1);
      newColLabelSet.insert(_alphaVarId);
    }
  }

#if SMDP
  cout << "D1" << endl;
  for (unsigned i = 0; i < d1ParameterDataContainer.size(); i++) {
    cout << d1ParameterDataContainer[i].toString() << endl;
  }

  cout << "\nD2" << endl;
  for (unsigned i = 0; i < d2ParameterDataContainer.size(); i++) {
    cout << d2ParameterDataContainer[i].toString() << endl;
  }
#endif

  // Create objective function by suming D2 without RHS
  LinearArithmeticDP::Constraint objectiveFunc;
  objectiveFunc.constant = RationalConstantType(0);
  objectiveFunc.parent = NULL;
  objectiveFunc.predicate = Interpretation::EQUAL;
  for (unsigned i = 0; i < d2ParameterDataContainer.size(); i++) {
    map<unsigned, RationalConstantType>::iterator it = d2ParameterDataContainer[i].parameters.begin();
    while (it != d2ParameterDataContainer[i].parameters.end()) {
      if (objectiveFunc.parameters.find(it->first) == objectiveFunc.parameters.end()) {
        if (!it->second.isZero()) {
          objectiveFunc.parameters[it->first] = it->second;
        }
      }
      else {
        objectiveFunc.parameters[it->first] = objectiveFunc.parameters[it->first] + it->second;
      }
      it++;
    }
  }

  // Creating constarants
  vector<LinearArithmeticDP::Constraint> newConstrains;
  for (unsigned i = 0; i < d1ParameterDataContainer.size(); i++) {
    newConstrains.push_back(d1ParameterDataContainer[i]);
  }
  for (unsigned i = 0; i < d2ParameterDataContainer.size(); i++) {
    newConstrains.push_back(d2ParameterDataContainer[i]);
  }

  _satOptimalValue = RationalConstantType(0);
  for (unsigned i = 0; i < d2ParameterDataContainer.size(); i++) {
    _satOptimalValue = _satOptimalValue + d2ParameterDataContainer[i].constant;
  }

  _simplexSolver = new Simplex(objectiveFunc, newConstrains, newColLabelSet);
  _status = LinearArithmeticDP::UNKNOWN;
}

void SimplexDP::solve()
{
  CALL("SimplexDP::solve");
  _simplexSolver->getStatus();
  if (_simplexSolver->getOptimalValue() != _satOptimalValue) {
    _status = DecisionProcedure::UNSATISFIABLE;
    return;
  }

  map<unsigned, RationalConstantType> model = _simplexSolver->getModel();
  if (model.find(_alphaVarId) != model.end() && !model[_alphaVarId].isPositive()) {
    _status = DecisionProcedure::UNSATISFIABLE;
    return;
  }

  _status = DecisionProcedure::SATISFIABLE;
}

DecisionProcedure::Status SimplexDP::getStatus()
{
  CALL("SimplexDP::getStatus");
  if (_status == LinearArithmeticDP::UNKNOWN) {
    solve();
  }

#if SMDP
  cout << "Status: " << (_status == DecisionProcedure::Status::SATISFIABLE ? "SAT" : "UNSAT") << endl;
#endif

  return _status;
}

void SimplexDP::getModel(LiteralStack &model)
{
  CALL("SimplexDP::getModel");
}

unsigned SimplexDP::getUnsatCoreCount()
{
  if (_status == LinearArithmeticDP::SATISFIABLE || _status == LinearArithmeticDP::UNKNOWN) {
    return 0;
  }
  else {
    return 1;
  }
}

set<unsigned> SimplexDP::getUnsatCore(unsigned coreIndex)
{
  if (_status == LinearArithmeticDP::SATISFIABLE || _status == LinearArithmeticDP::UNKNOWN || coreIndex > 0) {
    return set<unsigned>();
  }
  else {
    set<unsigned> unsat;
    for (unsigned i = 0; i < _simplexSolver->getRowCount(); i++) {
      unsat.insert(i);
    }
    return unsat;
  }
}

SimplexDP::~SimplexDP()
{
  CALL("SimplexDP::~SimplexDP");
}
} // namespace DP
