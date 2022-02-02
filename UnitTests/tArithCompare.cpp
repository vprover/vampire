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
#include "Test/TestUtils.hpp"
#include "Kernel/Theory.hpp"

using namespace std;
using namespace Lib;
using namespace Kernel;

TEST_FUN(testArithCompareSAT)
{
  IntegerConstantType cMAX(INT_MAX);
  IntegerConstantType cMIN(INT_MIN);
  IntegerConstantType cMINp(INT_MIN+1);
  IntegerConstantType cMINpp(INT_MIN+2);

  IntegerConstantType c2(2);
  IntegerConstantType cm1(-1);
  IntegerConstantType cm2(-2);

  ASS_EQ(IntegerConstantType::comparePrecedence(c2,cm1),GREATER);
  ASS_EQ(IntegerConstantType::comparePrecedence(cm1,cm2),LESS);
  ASS_EQ(IntegerConstantType::comparePrecedence(cm2,c2),GREATER);

  ASS_EQ(IntegerConstantType::comparePrecedence(cMIN,cMAX),GREATER);
  ASS_EQ(IntegerConstantType::comparePrecedence(cMAX,cMINp),LESS);
  ASS_EQ(IntegerConstantType::comparePrecedence(cMAX,cMINpp),GREATER);
}

