/**
 * @file RuntimeStatistics.hpp
 * Defines class RuntimeStatistics.
 */

#ifndef __UnitTesting__
#define __UnitTesting__

/**
Macros:
UNIT_ID        -- must be defined in the beginning of each unit test .cpp file. Unit IDs must be unique,
                  and must be valid variable names.
UT_CREATE      -- must be called after the definition of UNIT_ID
TEST_FUN(proc) -- replaces the usual function definition and creates test named @b proc in the current unit.
		  Due to the test framework, there is no need to use the CALL macro in the beginning of this
		  function.

If all works well, tests should not produce any output. If test should fail,
an assertion must be violated or an exception thrown.

A sample test file:

#include "Debug/Assertion.hpp"
#include "Test/UnitTesting.hpp"

#define UNIT_ID test1  //the UNIT_ID must be a valid variable name
UT_CREATE;

TEST_FUN(commTest)
{
  //there is no need to use the CALL macro at the beginning of a test function

  ASS_EQ(1+2,2+1);
}

TEST_FUN(assocTest)
{
  ASS_EQ(1+(2+3),(1+2)+3);
}

Execution:
make vtest

vtest		#this runs all tests
vtest -l	#this lists all test IDs
vtest test1	#this runs only test1
*/


#include <string.h>
#include <ostream>

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

#include "Lib/List.hpp"

namespace Test {

using namespace std;
using namespace Lib;

typedef void (*TestProc)();

class TestUnit
{
public:
  struct Test
  {
    Test() {}
    Test(TestProc proc, const char* name) : proc(proc), name(name) {}

    TestProc proc;
    const char* name;
  };

  typedef List<Test> TestList;
  typedef TestList::DestructiveIterator Iterator;

  TestUnit(const char* id);

  const char* id() { return _id; }

  void addTest(TestProc proc, const char* name)
  { TestList::push(Test(proc, name), _tests); }

  Iterator getTests();
private:
  const char* _id;

  TestList* _tests;
};

struct TU_Aux_Test_Adder
{
  TU_Aux_Test_Adder(TestUnit& tu, TestProc proc, const char* name)
  {
    tu.addTest(proc, name);
  }
};

class UnitTesting
{
private:
  typedef List<TestUnit*> TestUnitList;
public:
  static UnitTesting* instance();

  bool runTest(const char* unitId, ostream& out);
  void runAllTests(ostream& out);
  void printTestNames(ostream& out);

  void add(TestUnit* tu)
  { TestUnitList::push(tu, _units); }
private:
  UnitTesting();
  ~UnitTesting();

  TestUnit* get(const char* name);

  void runTest(TestUnit* unit, ostream& out);

  TestUnitList* _units;
};

#define UT_AUX_NAME__(ID) _ut_aux_##ID##_
#define UT_AUX_NAME_(ID) UT_AUX_NAME__(ID)
#define UT_AUX_NAME UT_AUX_NAME_(UNIT_ID)

#define UT_AUX_NAME_STR__(ID) #ID
#define UT_AUX_NAME_STR_(ID) UT_AUX_NAME_STR__(ID)
#define UT_AUX_NAME_STR UT_AUX_NAME_STR_(UNIT_ID)

#define UT_AUX_ADDER_NAME__(ID,LINE) _ut_aux_adder_##ID##_##LINE##_
#define UT_AUX_ADDER_NAME_(ID,LINE) UT_AUX_ADDER_NAME__(ID,LINE)
#define UT_AUX_ADDER_NAME UT_AUX_ADDER_NAME_(UNIT_ID, __LINE__)


#define UT_CREATE Test::TestUnit UT_AUX_NAME(UT_AUX_NAME_STR)

#define TEST_FUN(name)  void name(); \
			Test::TU_Aux_Test_Adder UT_AUX_ADDER_NAME(UT_AUX_NAME,name,#name); \
			void name()

}

#endif // __RuntimeStatistics__
