/*
 * File GaussElimination.cpp.
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
 * @file GaussElimination.cpp
 * Implements class GaussElimination.
 */
#define GEDP 1

#include "GaussElimination.hpp"

#include "Lib/List.hpp"
#include "Kernel/Sorts.hpp"

#include <iostream>
#include <vector>
#include <iterator>
#include <set>
#include <typeinfo>

namespace DP {

void printParameterList(List<LinearArithmeticDP::Parameter> *l)
{
  List<LinearArithmeticDP::Parameter> *current = l;
  while (!List<LinearArithmeticDP::Parameter>::isEmpty(current)) {
    std::cout << "ParameterID: " << current->head().varId << ", coefficient: " << current->head().coefficient << std::endl;
    current = current->tail();
  }
}

GaussElimination::GaussElimination(std::vector<List<LinearArithmeticDP::Parameter> *> rowsVector, std::set<unsigned int> colLabelSet)
{
  CALL("GaussElimination::GaussElimination");
  this->rowsList = new List<LinearArithmeticDP::Parameter> *[rowsVector.size()];
  for (unsigned int i = 0; i < rowsVector.size(); i++) {
    this->rowsList[i] = rowsVector[i];
  }
  this->numberOfRows = rowsVector.size();

  this->colLabelList = new unsigned[colLabelSet.size()];
  unsigned colLabelListIndex = 0;
  for (unsigned const &colLabel : colLabelSet) {
    colLabelList[colLabelListIndex++] = colLabel;
  }

  this->numberOfUnkowns = colLabelSet.size();

  this->solutions = NULL;
}

DecisionProcedure::Status GaussElimination::getStatus()
{
  CALL("GaussElimination::solve");
  List<LinearArithmeticDP::Parameter> **newRowsList = new List<LinearArithmeticDP::Parameter> *[numberOfRows];

  std::set<unsigned int> rowsLeftIndex;
  for (unsigned int i = 0; i < numberOfRows; i++)
    rowsLeftIndex.insert(i);

  numberOfRows = 0;
  for (unsigned int i = 0; i < numberOfUnkowns; i++) {
    unsigned int colLabel = colLabelList[i];

    std::vector<unsigned int> rowsIndexWithNonZero;
    for (auto &rowIndex : rowsLeftIndex) {
      if (!getCoefficient(rowsList[rowIndex], colLabel).isZero()) {
        rowsIndexWithNonZero.emplace_back(rowIndex);
      }
    }

    if (rowsIndexWithNonZero.size() != 0) {
      unsigned int pivotIndex = rowsIndexWithNonZero[0];
      rowsLeftIndex.erase(pivotIndex);
      newRowsList[numberOfRows++] = rowsList[pivotIndex];

      for (unsigned int j = 1; j < rowsIndexWithNonZero.size(); j++) {
        int rowIndex = rowsIndexWithNonZero[j];
        RationalConstantType multiplier = getCoefficient(rowsList[rowIndex], colLabel) / getCoefficient(rowsList[pivotIndex], colLabel);

        // subtract
        rowsList[rowIndex] = subtract(rowsList[rowIndex], rowsList[pivotIndex], multiplier);
      }
    }
  }

  // There are some leftover rows. Some are all zeros -> disregard. Others, check for satifiability
  for (auto &rowIndex : rowsLeftIndex) {
    List<LinearArithmeticDP::Parameter> *row = rowsList[rowIndex];
    if (row->head().varId == UINT_MAX && !row->head().coefficient.isZero()) {

#if GEDP
      std::cout << "Unsatisfiable: ";
      printParameterList(row);
#endif

      return DecisionProcedure::UNSATISFIABLE;
    }
    List<LinearArithmeticDP::Parameter>::destroy(row);
  }

#if GEDP
  for (unsigned int i = 0; i < numberOfRows; i++) {
    printParameterList(newRowsList[i]);
    std::cout << std::endl;
  }
#endif

  // At this point satisfiable. Possibly infinite solutions
  delete[] rowsList;
  rowsList = newRowsList;

  // if matrix is triangular form use back subsitution
  if (numberOfRows < numberOfUnkowns) {
#if GEDP
    std::cout << "Satisfiable with infinite solutions as number of equations < number of unkowns." << std::endl;
#endif
    return DecisionProcedure::SATISFIABLE;
  }

  solutions = new RationalConstantType[numberOfUnkowns];
  // At this point, matrix in upper triangular form
  for (int i = numberOfUnkowns - 1; i >= 0; i--) {
    List<LinearArithmeticDP::Parameter> *row = newRowsList[i];
    solutions[i] = RationalConstantType(0);
    List<LinearArithmeticDP::Parameter> *current = row->tail();
    unsigned int m = i + 1;

    while (!List<LinearArithmeticDP::Parameter>::isEmpty(current->tail())) {
      m = getColLabelIndex(current->head().varId, m);
      solutions[i] = solutions[i] - current->head().coefficient * solutions[m];
      m++;
      current = current->tail();
    }
    solutions[i] = current->head().coefficient + solutions[i];
    solutions[i] = solutions[i] / row->head().coefficient;
  }

#if GEDP
  for (unsigned int i = 0; i < numberOfUnkowns; i++) {
    std::cout << "Varid: " << colLabelList[i] << " = " << solutions[i] << std::endl;
  }
#endif

  return DecisionProcedure::SATISFIABLE;
}

RationalConstantType GaussElimination::getCoefficient(List<LinearArithmeticDP::Parameter> *row, unsigned int varId)
{
  CALL("GaussElimination::getCoefficient");
  List<LinearArithmeticDP::Parameter> *current = row;
  while (!List<LinearArithmeticDP::Parameter>::isEmpty(current)) {
    if (current->head().varId == varId)
      return current->head().coefficient;

    if (current->head().varId > varId)
      break;

    current = current->tail();
  }

  return RationalConstantType(0);
}

// e1 = e1 - multiplier*e2
List<LinearArithmeticDP::Parameter> *GaussElimination::subtract(List<LinearArithmeticDP::Parameter> *e1, List<LinearArithmeticDP::Parameter> *e2, RationalConstantType multiplier)
{
  CALL("GaussElimination::subtract");
  List<LinearArithmeticDP::Parameter> *currentE1 = e1->tail();
  List<LinearArithmeticDP::Parameter> *previousE1 = e1;
  List<LinearArithmeticDP::Parameter> *currentE2 = e2->tail();
  while (!List<LinearArithmeticDP::Parameter>::isEmpty(currentE2)) {
    if (currentE1->head().varId == currentE2->head().varId) {
      unsigned varId = currentE2->head().varId;
      RationalConstantType coefficient = currentE1->head().coefficient - (multiplier * currentE2->head().coefficient);
      LinearArithmeticDP::Parameter elm = LinearArithmeticDP::Parameter(varId, coefficient);
      currentE1->setHead(elm);

      if (elm.coefficient.isZero() && elm.varId != UINT_MAX) {
        previousE1->setTail(currentE1->tail());
        delete currentE1;
        currentE1 = previousE1;
      }

      currentE2 = currentE2->tail();
    }
    else if (currentE1->tail()->head().varId > currentE2->head().varId) {
      // Inserting new elm
      unsigned varId = currentE2->head().varId;
      RationalConstantType coefficient = RationalConstantType(-1) * multiplier * currentE2->head().coefficient;
      LinearArithmeticDP::Parameter elm = LinearArithmeticDP::Parameter(varId, coefficient);

      List<LinearArithmeticDP::Parameter> *listElm = new List<LinearArithmeticDP::Parameter>(elm, currentE1->tail());
      currentE1->setTail(listElm);

      previousE1 = currentE1;
      currentE1 = currentE1->tail();
      currentE2 = currentE2->tail();
    }
    else {
      previousE1 = currentE1;
      currentE1 = currentE1->tail();
    }
  }

  return e1->tail();
}

void GaussElimination::getModel(LiteralStack &model)
{
  CALL("GaussElimination::getModel");
#if GEDP
  cout << "GaussElimination::getModel" << endl;
#endif
  if (solutions == NULL)
    return;

  for (unsigned i = 0; i < numberOfUnkowns; i++) {
    unsigned varId = colLabelList[i];
    RationalConstantType solution = solutions[i];
    unsigned sort = env.signature->getFunction(varId)->fnType()->result();
    switch (sort) {
      case Sorts::SRT_INTEGER: {
        if (!solution.isInt())
          continue;

        Term *var = Term::createConstant(varId);
        Term *constant = theory->representConstant(IntegerConstantType(solution.numerator()));
        Literal *lit = Literal::createEquality(true, TermList(var), TermList(constant), sort);
        cout << lit->toString() << endl;
        model.push(lit);
      } break;
      case Sorts::SRT_RATIONAL: {
        Term *var = Term::createConstant(varId);
        Term *constant = theory->representConstant(solution);
        Literal *lit = Literal::createEquality(true, TermList(var), TermList(constant), sort);
        cout << lit->toString() << endl;
        model.push(lit);
      } break;
      case Sorts::SRT_REAL: {
        Term *var = Term::createConstant(varId);
        Term *constant = theory->representConstant(RealConstantType(solution));
        Literal *lit = Literal::createEquality(true, TermList(var), TermList(constant), sort);
        #if GEDP
        cout << lit->toString() << endl;
        #endif
        model.push(lit);
      } break;
      default:
        continue;
        break;
    }
  }
}

int GaussElimination::getColLabelIndex(unsigned int label, unsigned int searchStartIndex)
{
  CALL("GaussElimination::getColLabelIndex");
  for (unsigned int i = searchStartIndex; i < numberOfUnkowns; i++) {
    if (colLabelList[i] == label) {
      return i;
    }
  }
  return -1;
}

GaussElimination::~GaussElimination()
{
  CALL("GaussElimination::~GaussElimination");
  for (int i = 0; i < numberOfRows; i++) {
    List<LinearArithmeticDP::Parameter>::destroy(rowsList[i]);
  }

  delete[] rowsList;
  if (solutions != NULL) {
    delete[] solutions;
  }
  delete[] colLabelList;
}
} // namespace DP
