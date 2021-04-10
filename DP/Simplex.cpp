/*
 * File Simplex.cpp.
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
 * @file Simplex.cpp
 * Implements class Simplex procedure.
 */

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "DP/LinearArithmeticDP.hpp"
#include "DP/Simplex.hpp"

#define SMDP DLADP

namespace DP {

void printTableau(RationalConstantType **tableau, unsigned rowCount, unsigned colCount)
{
  CALL("Simplex::printTableau");
  for (unsigned i = 0; i < rowCount; i++) {
    cout << "[";
    for (unsigned j = 0; j < colCount; j++) {
      string number;
      if (tableau[i][j].isInt()) {
        number = to_string(tableau[i][j].numerator().toInner());
      }
      else {
        number = tableau[i][j].toString().c_str();
      }

      cout << number << ",\t";
    }
    cout << "]" << endl;
  }
}

void printStatus(Simplex::Status status)
{
  CALL("Simplex::printStatus");
  switch (status) {
    case Simplex::Optimal: {
      cout << "Optimal solution found" << endl;
    } break;
    case Simplex::Unbounded: {
      cout << "Probelm Unbounded" << endl;
    }
    default:
      break;
  }
}

static bool quotientCompare(tuple<unsigned, RationalConstantType> &first, tuple<unsigned, RationalConstantType> &second)
{
  return get<1>(first) < get<1>(second);
}

Simplex::Simplex(LinearArithmeticDP::Constraint objectiveFunc, vector<LinearArithmeticDP::Constraint> constraints, set<unsigned> colLabelSet)
{
  CALL("Simplex::Simplex");

  _varLabelSet = colLabelSet;

  // Setting up tableau. The first row of the tableau is the objective function
  _rowCount = constraints.size() + 1;
  _colCount = colLabelSet.size() + _rowCount;
  _tableau = new RationalConstantType *[_rowCount];
  for (unsigned i = 0; i < _rowCount; i++) {
    _tableau[i] = new RationalConstantType[_colCount];
  }
  for (unsigned i = 0; i < _rowCount; i++) {
    for (unsigned j = 0; j < _colCount; j++) {
      _tableau[i][j] = RationalConstantType(0);
    }
  }

  // Setting up objective function row
  unsigned tableauColIndex = 0;
  for (auto &colLabel : colLabelSet) {
    if (objectiveFunc.parameters.find(colLabel) != objectiveFunc.parameters.end()) {
      _tableau[0][tableauColIndex] = -objectiveFunc.parameters[colLabel];
    }

    tableauColIndex++;
  }

  // Setting up constraints function
  for (unsigned rowIndex = 1; rowIndex < _rowCount; rowIndex++) {
    tableauColIndex = 0;
    LinearArithmeticDP::Constraint *currentRow = &constraints[rowIndex - 1];
    for (auto &colLabel : colLabelSet) {
      if (currentRow->parameters.find(colLabel) != currentRow->parameters.end()) {
        _tableau[rowIndex][tableauColIndex] = currentRow->parameters[colLabel];
      }
      tableauColIndex++;
    }
    _tableau[rowIndex][_colCount - 1] = currentRow->constant;

    // Add slack variable coef
    _tableau[rowIndex][colLabelSet.size() + (rowIndex - 1)] = RationalConstantType(1);
  }

  _status = Simplex::Undefined;
}

void Simplex::solve()
{
  CALL("Simplex::solve");
#if SMDP
  cout << "Intial Tableau:" << endl;
  printTableau(_tableau, _rowCount, _colCount);
#endif
  while (canImprove()) {
    // Finding pivot index
    // Picking the minimum positive index of the objective function (first row).
    unsigned colIndex;
    RationalConstantType currentSmallestCoefficient = RationalConstantType(0);
    for (unsigned i = 0; i < _colCount - 1; i++) {
      if (_tableau[0][i] < currentSmallestCoefficient) {
        colIndex = i;
        currentSmallestCoefficient = _tableau[0][i];
      }
    }

    unsigned rowIndex;
    // Check for degeneracy: more than one minimizer of the quotient
    vector<tuple<unsigned, RationalConstantType>> quotients;
    for (unsigned i = 1; i < _rowCount; i++) {
      if (_tableau[i][colIndex].isPositive()) {
        quotients.push_back(tuple<unsigned, RationalConstantType>(i, _tableau[i][_colCount - 1] / _tableau[i][colIndex]));
      }
    }

    if (quotients.size() < 1) {
      // Problem is unbounded
      _status = Simplex::Unbounded;
      break;
    }
    else if (quotients.size() == 1) {
      rowIndex = get<0>(quotients[0]);
    }
    else {
      sort(quotients.begin(), quotients.end(), quotientCompare);
      rowIndex = get<0>(quotients[0]);
    }

#if SMDP
    cout << "Pivoting at col:" << colIndex << ", row:" << rowIndex << endl
         << endl;
#endif
    pivotAbout(rowIndex, colIndex);

#if SMDP
    printTableau(_tableau, _rowCount, _colCount);
#endif
  }

  if (_status == Simplex::Undefined) {
    _status = Simplex::Optimal;
  }

#if SMDP
  printStatus(_status);
#endif
}

bool Simplex::canImprove()
{
  CALL("Simplex::canImprove");
  for (unsigned i = 0; i < _colCount - 1; i++) {
    if (_tableau[0][i].isNegative())
      return true;
  }
  return false;
}

void Simplex::pivotAbout(unsigned pivotRow, unsigned pivotCol)
{
  CALL("Simplex::pivotAbout");
  RationalConstantType pivotDenominator = _tableau[pivotRow][pivotCol];
  for (unsigned colIndex = 0; colIndex < _colCount; colIndex++) {
    _tableau[pivotRow][colIndex] = _tableau[pivotRow][colIndex] / pivotDenominator;
  }

  unsigned rowIndex;
  for (rowIndex = 0; rowIndex < pivotRow; rowIndex++) {
    RationalConstantType multiplier = -_tableau[rowIndex][pivotCol];
    for (unsigned colIndex = 0; colIndex < _colCount; colIndex++) {
      _tableau[rowIndex][colIndex] = multiplier * _tableau[pivotRow][colIndex] + _tableau[rowIndex][colIndex];
    }
  }

  for (rowIndex = pivotRow + 1; rowIndex < _rowCount; rowIndex++) {
    RationalConstantType multiplier = -_tableau[rowIndex][pivotCol];
    for (unsigned colIndex = 0; colIndex < _colCount; colIndex++) {
      _tableau[rowIndex][colIndex] = multiplier * _tableau[pivotRow][colIndex] + _tableau[rowIndex][colIndex];
    }
  }
}

Simplex::Status Simplex::getStatus()
{
  CALL("Simplex::getStatus");
  solve();
  return _status;
}

RationalConstantType Simplex::getOptimalValue()
{
  return _tableau[0][_colCount - 1];
}

map<unsigned, RationalConstantType> Simplex::getModel()
{
  map<unsigned, RationalConstantType> solutionMap;
  // if non zero in objective function then its value is zero
  // otherwise findind it in row and set to righthand side

  unsigned colIndex = 0;
  for (unsigned const &varLabel : _varLabelSet) {
    unsigned rowIndex;
    for (rowIndex = 0; rowIndex < _rowCount; rowIndex++) {
      if (!_tableau[rowIndex][colIndex].isZero()) {
        break;
      }
    }

    solutionMap[varLabel] = (rowIndex == 0) ? RationalConstantType(0) : _tableau[rowIndex][_colCount - 1];
    colIndex++;
  }

  return solutionMap;
}

RationalConstantType Simplex::getModel(unsigned varId)
{
  if (_varLabelSet.find(varId) == _varLabelSet.end()) {
    ASSERTION_VIOLATION;
  }

  unsigned varIdColIndex = 0;
  for (unsigned const &varLabel : _varLabelSet) {
    if (varLabel == varId) {
      break;
    }

    varIdColIndex++;
  }

  unsigned rowIndex;
  for (rowIndex = 0; rowIndex < _rowCount; rowIndex++) {
    if (!_tableau[rowIndex][varIdColIndex].isZero()) {
      break;
    }
  }

  return (rowIndex == 0) ? RationalConstantType(0) : _tableau[rowIndex][_colCount - 1];
}

unsigned Simplex::getRowCount()
{
  return _rowCount - 1;
}

Simplex::~Simplex()
{
  CALL("Simplex::~Simplex");
  for (unsigned i = 0; i < _rowCount; i++) {
    delete[] _tableau[i];
  }

  delete[] _tableau;
}
} // namespace DP