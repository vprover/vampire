#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Debug/Tracer.hpp"

#include <climits>

#define UNIT_ID QuotientE
UT_CREATE;
#define DBGE(x) DBG(#x, "\t=\t", x)

IntegerConstantType quotientE(int lhs, int rhs) {
  return IntegerConstantType(lhs).quotientE(rhs);
}

IntegerConstantType remainderE(int lhs, int rhs) {
  return IntegerConstantType(lhs).remainderE(rhs);
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

TEST_FUN(check_spec) {
  for (int j = std::numeric_limits<int>::min();;) {
    for (int i = std::numeric_limits<int>::min();; ) {


        bool bothOK = true;

        IntegerConstantType q;
        try {
          q = quotientE(i, j);
          // DBG("quotientE (", i,", ", j,")\t= ", q);
        } catch (const MachineArithmeticException&) {
          // DBG("quotientE (", i,", ", j,")\t= MachineArithmeticException");
          bothOK = false;
        }

        IntegerConstantType r;
        try {
	 r = remainderE(i, j);
         // DBG("remainderE(", i,", ", j,")\t= ", r);
	} catch (const MachineArithmeticException&) {
	 // DBG("remainderE(", i,", ", j,")\t= MachineArithmeticException");
	 bothOK = false;
	}

        if (bothOK) {
          // do the math 64 bit
          long long int I = i;
          long long int J = j;
          long long int Q = q.toInner();
          long long int R = r.toInner();

          ASS_EQ(Q * J + R, I)
          ASS(0 <= R && R < abs(J))
        }

      if (i == std::numeric_limits<int>::max()) {
        break;
      } else {
        i++;
      }
      // fast forward closer to zero
      if (i == std::numeric_limits<int>::min()+100) {
        i = -100;
      }
      // fast forward closer to max
      if (i == 100) {
        i = std::numeric_limits<int>::max()-100;
      }
    }

    if (j == std::numeric_limits<int>::max()) {
      break;
    } else {
      j++;
    }
    // fast forward closer to zero
    if (j == std::numeric_limits<int>::min()+100) {
      j = -100;
    }
    // fast forward closer to max
    if (j == 100) {
      j = std::numeric_limits<int>::max()-100;
    }
  }
}

