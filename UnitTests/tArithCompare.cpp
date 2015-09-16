

#include "Test/UnitTesting.hpp"
#include "Kernel/Theory.hpp"

#define UNIT_ID arithCompareTest
UT_CREATE;

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
  IntegerConstantType c1(1);
  IntegerConstantType c0(0);
  IntegerConstantType cm1(-1);
  IntegerConstantType cm2(-2);

  ASS_EQ(IntegerConstantType::comparePrecedence(c2,cm1),GREATER);
  ASS_EQ(IntegerConstantType::comparePrecedence(cm1,cm2),LESS);
  ASS_EQ(IntegerConstantType::comparePrecedence(cm2,c2),GREATER);

  ASS_EQ(IntegerConstantType::comparePrecedence(cMIN,cMAX),GREATER);
  ASS_EQ(IntegerConstantType::comparePrecedence(cMAX,cMINp),LESS);
  ASS_EQ(IntegerConstantType::comparePrecedence(cMAX,cMINpp),GREATER);
}

