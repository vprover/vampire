#include <iostream>
#include "Debug/Assertion.hpp"
#include "Lib/RatioKeeper.hpp"

#include "Test/UnitTesting.hpp"

#define UNIT_ID rkeeper
UT_CREATE;

using namespace std;
using namespace Lib;

TEST_FUN(rkeeper1)
{

//  RatioKeeper rkeeper(1,2,5);
  RatioKeeper rkeeper(2,1,5); //the two ratios are reversed, when it's fixed, use the above line instead of this

  int ones = 0;
  int twos = 0;

  for(unsigned i=0; i<3000; i++) {
    if(rkeeper.shouldDoFirst()) {
      rkeeper.doFirst();
      ones++;
    }
    else {
      ALWAYS(rkeeper.shouldDoSecond());
      rkeeper.doSecond();
      twos++;
    }
  }
  ASS_G(ones, 994);
  ASS_L(ones, 1006);
  ASS_G(twos, 1994);
  ASS_L(twos, 2006);
}
