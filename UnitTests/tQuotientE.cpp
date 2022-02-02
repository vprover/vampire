/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Debug/Tracer.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#include <climits>

#define DEBUG(...) //DBG(__VA_ARGS__)
#define DEBUGE(x) DEBUG(#x, " = ", x)

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
    for (int i = std::numeric_limits<int>::min();;) {

      DEBUG();

      bool bothOK = true;

      IntegerConstantType q;
      try {
        q = quotientE(i, j);
        DEBUG("quotientE (", i, ", ", j, ")\t= ", q);
      } catch (MachineArithmeticException&) {
        DEBUG("quotientE (", i, ", ", j, ")\t= MachineArithmeticException");
        bothOK = false;
      } catch (DivByZeroException&) {
        ASS_EQ(j, 0);
        bothOK = false;
      }

      IntegerConstantType r;
      try {
        r = remainderE(i, j);
        DEBUG("remainderE(", i, ", ", j, ")\t= ", r);
      } catch (MachineArithmeticException&) {
        DEBUG("remainderE(", i, ", ", j, ")\t= MachineArithmeticException");
        bothOK = false;
      } catch (DivByZeroException&) {
        ASS_EQ(j, 0);
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
    if (j == std::numeric_limits<int>::min() + 100) {
      j = -100;
    }
    // fast forward closer to max
    if (j == 100) {
      j = std::numeric_limits<int>::max() - 100;
    }
  }
}

template<class Const>
void checkQuotientE(Const i, Const j) {
  try {
    DEBUG()
    auto q =  i.quotientE(j);
    auto r = i.remainderE(j);

    DEBUG(" quotientE(", i, ", ", j, ")\t= ", q);
    DEBUG("remainderE(", i, ", ", j, ")\t= ", r);
    ASS_EQ(q * j + r, i)
    ASS(Const(0) <= r && r < j.abs())
  } catch (DivByZeroException&) {
    ASS_EQ(j,Const(0))
  }
}

TEST_FUN(check_int) 
{
  int range = 10;
  for (int i = -range; i < range; i++) {
    for (int j = -range; j < range; j++) {
      checkQuotientE(IntegerConstantType(i), IntegerConstantType(j));
    }
  }
}

// REMOVED until there are benchmarks that actually use (quotient|remainder)_(e|t|r) with non-integral number types
//
// template<class Const>
// void checkQuotientEFrac() 
// {
//   int range = 10;
//   for (int i = -range; i < range; i++) {
//     for (int j = -range; j < range; j++) {
//       for (int k = -range; k < range; k++) {
//         for (int l = -range; l < range; l++) {
//           if (j != 0 && l != 0) {
//             checkQuotientE(Const(i, j), Const(k, l));
//           }
//         }
//       }
//     }
//   }
// }
//
// TEST_FUN(check_real) 
// { checkQuotientEFrac<RealConstantType>(); }
//
// TEST_FUN(check_rat) 
// { checkQuotientEFrac<RationalConstantType>(); }

template<class Const>
void checkFloor() 
{
  ASS_EQ(Const( 3, 2).floor(), Const( 1))
  ASS_EQ(Const(-3, 2).floor(), Const(-2))
  ASS_EQ(Const( 4, 2).floor(), Const( 2))
  ASS_EQ(Const(-4, 2).floor(), Const(-2))
  ASS_EQ(Const( 0, 2).floor(), Const( 0))
}

template<class Const>
void checkCeiling() 
{
  ASS_EQ(Const( 3, 2).ceiling(), Const( 2))
  ASS_EQ(Const(-3, 2).ceiling(), Const(-1))
  ASS_EQ(Const( 4, 2).ceiling(), Const( 2))
  ASS_EQ(Const(-4, 2).ceiling(), Const(-2))
  ASS_EQ(Const( 0, 2).ceiling(), Const( 0))
}


#define CHECK_FRAC(Const) \
  TEST_FUN(check_ceiling_##Const) { checkCeiling<Const>(); } \
  TEST_FUN(check_floor_  ##Const) { checkFloor  <Const>(); } \

CHECK_FRAC(RationalConstantType)
CHECK_FRAC(RealConstantType)
