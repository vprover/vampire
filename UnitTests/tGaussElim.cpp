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

#include "Lib/List.hpp"

UT_CREATE;
using namespace std;
using namespace Kernel;
using namespace Inferences;

#include "Test/SyntaxSugar.hpp"

void printParameterList(List<DP::LinearArithmeticDP::Parameter> *l)
{
  List<DP::LinearArithmeticDP::Parameter> *current = l;
  while (!List<DP::LinearArithmeticDP::Parameter>::isEmpty(current)) {
    std::cout << "ParameterID: " << current->head().varId << ", coefficient: " << current->head().coefficient << std::endl;
    current = current->tail();
  }
}

//e1 = e1 - multiplier*e2
List<DP::LinearArithmeticDP::Parameter>* subtract(List<DP::LinearArithmeticDP::Parameter> *e1, List<DP::LinearArithmeticDP::Parameter> *e2, float multiplier)
{
  printParameterList(e1);
  printParameterList(e2);

  List<DP::LinearArithmeticDP::Parameter> *currentE1 = e1->tail();
  List<DP::LinearArithmeticDP::Parameter> *previousE1 = e1;
  List<DP::LinearArithmeticDP::Parameter> *currentE2 = e2->tail();
  while (!List<DP::LinearArithmeticDP::Parameter>::isEmpty(currentE2)) {
    if (currentE1->head().varId == currentE2->head().varId) {
      unsigned varId = currentE2->head().varId;
      float coefficient = currentE1->head().coefficient - (multiplier * currentE2->head().coefficient);
      DP::LinearArithmeticDP::Parameter elm = DP::LinearArithmeticDP::Parameter(varId, coefficient);
      currentE1->setHead(elm);

      if (elm.coefficient == 0 && elm.varId != UINT_MAX) {
          previousE1->setTail(currentE1->tail());
          currentE1 = previousE1;
      }

      currentE2 = currentE2->tail();
    }
    else if (currentE1->tail()->head().varId > currentE2->head().varId) {
      // Inserting new elm
      unsigned varId = currentE2->head().varId;
      float coefficient = -1 * multiplier * currentE2->head().coefficient;
      DP::LinearArithmeticDP::Parameter elm = DP::LinearArithmeticDP::Parameter(varId, coefficient);
    
      List<DP::LinearArithmeticDP::Parameter> *listElm = new List<DP::LinearArithmeticDP::Parameter>(elm, currentE1->tail());
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

void test_list()
{
  std::cout << "\n\n#########################################################" << std::endl;
  std::vector<std::vector<float>> rowVector = {{0, 2, 4}, {0, 2, 4}, {1,1,7}};

  std::set<unsigned int> colLabelSet;
  std::vector<List<DP::LinearArithmeticDP::Parameter> *> rowsList;

  int i, k, j;
  for (i = 0; i < rowVector.size(); i++) {
    if (rowVector[i].size() < 1)
      continue;

    List<DP::LinearArithmeticDP::Parameter> *rowList = 0;
    for (k = 0; k < rowVector[i].size(); k++) {
      if (rowVector[i][k] != 0) {
        unsigned varId = k * 2;
        float coefficient = rowVector[i][k];
        DP::LinearArithmeticDP::Parameter elm  = DP::LinearArithmeticDP::Parameter(varId, coefficient);
        colLabelSet.insert(elm.varId);
  
        rowList = new List<DP::LinearArithmeticDP::Parameter>(elm);
        k++;
        break;
      }
    }

    List<DP::LinearArithmeticDP::Parameter> *current = rowList;
    for (j = k; j < rowVector[i].size() - 1; j++) {
      if (rowVector[i][j] != 0) {
        unsigned varId = j * 2;
        float coefficient = rowVector[i][j];
        DP::LinearArithmeticDP::Parameter elm = DP::LinearArithmeticDP::Parameter(varId, coefficient);
        colLabelSet.insert(elm.varId);

        current->setTail(new List<DP::LinearArithmeticDP::Parameter>(elm));
        current = current->tail();
      }
    }

    float coefficient = rowVector[i][rowVector[i].size() - 1];
    DP::LinearArithmeticDP::Parameter elm = DP::LinearArithmeticDP::Parameter(UINT_MAX, coefficient);
    current->setTail(new List<DP::LinearArithmeticDP::Parameter>(elm));

    rowsList.push_back(rowList);
  }

  /*
  // Printing
  for (int i = 0; i < rowsList.size(); i++) {
    std::cout << "Printing row " << i << std::endl;
    printParameterList(rowsList[i]);
  }
  */

  //std::cout << "Running GE" << std::endl;

  // Rowlist, col Label list, number of unknows
  DP::GaussElimination ge = DP::GaussElimination(rowsList, colLabelSet);
  ge.getStatus();
  
  //rowsList[1] = subtract(rowsList[1], rowsList[0], 2);
  //std::cout << "*****************"
  //          << std::endl;
  //printParameterList(rowsList[1]);
  
  std::cout << "#########################################################\n"
            << std::endl;


}

TEST_FUN(test_1)
{
  // x = 1 create term
  Literal lit = Literal::createEquality(true, TermList(Term* t), TermList arg2, unsigned sort)
  exit(-1);
}
