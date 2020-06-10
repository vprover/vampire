#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Debug/Tracer.hpp"

#define UNIT_ID QuotientE
UT_CREATE;
#define DBGE(x) DBG(#x, "\t=\t", x)

IntegerConstantType quotientE(int lhs, int rhs) {
  return IntegerConstantType(lhs).quotientE(rhs);
}

IntegerConstantType remainderE(int lhs, int rhs) {
  return IntegerConstantType(lhs) - (IntegerConstantType(lhs).quotientE(rhs) * IntegerConstantType(rhs));
}

bool operator==(IntegerConstantType lhs, int rhs) {
  return lhs == IntegerConstantType(rhs);
}

bool operator==(int lhs, IntegerConstantType rhs) {
  return IntegerConstantType(lhs) == rhs;
}

bool operator<=(int lhs, IntegerConstantType rhs) {
  return IntegerConstantType(lhs) <= rhs;
}

TEST_FUN(test_00) {
  for (int i = -100; i < 100; i++) {
    for (int j = -100; j < 100; j++) {
      if (j != 0) {
        // DBGE(i)
        // DBGE(j)
        DBG();
        auto q = quotientE(i, j);
        auto r = remainderE(i, j);
        DBG("quotientE (", i,", ", j,")\t= ", q);
        DBG("remainderE(", i,", ", j,")\t= ", r);
        ASS_EQ(q * j + r, i)
        ASS(0 <= r && r < abs(j))
      }
    }
  }
}



