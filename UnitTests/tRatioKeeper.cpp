/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include <iostream>
#include "Debug/Assertion.hpp"
#include "Lib/RatioKeeper.hpp"

#include "Test/UnitTesting.hpp"

using namespace std;
using namespace Lib;

TEST_FUN(rkeeper1)
{

  RatioKeeper rkeeper(1,2,5);

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
