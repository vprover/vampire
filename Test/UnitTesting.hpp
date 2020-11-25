
/*
 * File UnitTesting.hpp.
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
 * @file UnitTesting.hpp
 * Defines macros for testing
 */

#ifndef __UnitTesting__
#define __UnitTesting__

#include <string.h>
#include <ostream>


#include "Forwards.hpp"
#include "Lib/Stack.hpp"
#include "Debug/Tracer.hpp"


namespace Test {

using namespace std;
using namespace Lib;

typedef void (*TestProc)();

class TestUnit
{
  static TestUnit _instance;
public:
  static TestUnit& instance();
  struct Test
  {
    Test() {}
    Test(TestProc proc, const char* name) : proc(proc), name(name) {}

    TestProc proc;
    const char* name;
  };

  TestUnit();

  void add(Test);

  /** Runs all tests of this TestUnit
   *
   * returns true iff all tests of the unit were successfull.
   */
  bool run(ostream& out);

private:
  /** Runs a test as a single process and awaits its termination.
   * This is to provide isolation when running multiple tests in one go.
   *
   *  returns true iff the test process exited with status code 0
   */
  bool spawnTest(TestProc proc);

  Stack<Test> _tests;
};

struct TU_Aux_Test_Adder
{
  TU_Aux_Test_Adder(TestUnit& tu, TestProc proc, const char* name)
  {
    tu.add(TestUnit::Test(proc, name));
  }
};

#define UT_AUX_NAME__(ID) _ut_aux_##ID##_
#define UT_AUX_NAME_(ID) UT_AUX_NAME__(ID)
#define UT_AUX_NAME UT_AUX_NAME_(UNIT_ID)

#define UT_AUX_NAME_STR__(ID) #ID
#define UT_AUX_NAME_STR_(ID) UT_AUX_NAME_STR__(ID)
#define UT_AUX_NAME_STR UT_AUX_NAME_STR_(UNIT_ID)

#define UT_AUX_ADDER_NAME__(ID,LINE,NAME) _ut_aux_adder_##ID##_##LINE##_##NAME##_
#define UT_AUX_ADDER_NAME_(ID,LINE,NAME) UT_AUX_ADDER_NAME__(ID,LINE,NAME)
#define UT_AUX_ADDER_NAME(NAME) UT_AUX_ADDER_NAME_(UNIT_ID, __LINE__,NAME)

#define TEST_FUN(name)                                                                                        \
    void name();                                                                                              \
    Test::TU_Aux_Test_Adder UT_AUX_ADDER_NAME(name)(Test::TestUnit::instance(),name,#name);                                  \
    void name()

} // namespace Test

int main();

#endif // __UnitTesting__
