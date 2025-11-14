/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**!  This file contains examples on how to use Test/SyntaxSugar.hpp.
 *
 * @author Johannes Schoisswohl
 * @date 2022-07-11
 */

#include "Test/UnitTesting.hpp"
#include "Shell/Statistics.hpp"
#include "Debug/TimeProfiling.hpp"
#include "Lib/Environment.hpp"
using namespace Shell;

void fun02() { TIME_TRACE("fun02") }
void fun04() { TIME_TRACE("fun04") }
void fun03() {
  TIME_TRACE("fun03")
  for (unsigned i = 0; i < 3; i++) {
        fun04();
  }
}
void fun01(unsigned i2, unsigned i3) { 
  TIME_TRACE("fun01") 
  for (unsigned i = 0; i < i2; i++) {
    fun02();
  }
  for (unsigned i = 0; i < i3; i++) {
    fun03();
  }
}

TEST_FUN(test01) {
  TIME_TRACE("test01")
  fun01(7, 2);
  fun01(0, 2);
  fun01(8, 0);
  fun02();
  env.statistics->print(std::cout);
}
