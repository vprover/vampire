
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

/**

The way testing work is as follows.

<ol>
  <li> You should create a test file, say TestFile.cpp in the UnitTests directory of the Vampire
	tree. The test file must define <b>the test id</b> and one or more <b>test functions</b>.</li>

	<li>Update the definition of VUT_OBJ in the Makefile by adding TestFile.o</li>

	<li>To build the test with debugging use <span style='color:red'>make vtest</span>
	and without debugging <span style='color:red'>make vtest_rel</span>.</li>

	<li>Call the test using <span style='color:red'>vtest test_id</span>. The call will execute
	all the test functions in the file.</li>
</ol>
The following macros should be used:
<dl>
  <dt>UNIT_ID</dt>
    <dd>must be defined in the beginning of each unit test .cpp file. Unit IDs must be unique,
		and must be valid variable names</dd>
  <dt>UT_CREATE</dt>
    <dd>must be called after the definition of UNIT_ID</dd>
	<dt>TEST_FUN(proc)</dt>
	  <dd>used to declare a function of the type void->void with the name proc.
		Due to the test framework, there is no need to use the CALL macro in the beginning of this
		function.</dd>
</dl>

If all works well, tests should not produce any output. If test should fail,
an assertion must be violated or an exception thrown.

A sample test file:

<code><tt>
\#include "Debug/Assertion.hpp"<br/>
\#include "Test/UnitTesting.hpp"<br/>
<br/>
\#define UNIT_ID test1  //the UNIT_ID must be a valid variable name<br/>
UT_CREATE;<br/>
<br/>
TEST_FUN(commTest)<br/>
{<br/>
&nbsp;&nbsp;//there is no need to use the CALL macro at the beginning of a test function<br/>
<br/>
&nbsp;&nbsp;ASS_EQ(1+2,2+1);<br/>
}<br/>
<br/>
TEST_FUN(assocTest)<br/>
{<br/>
&nbsp;&nbsp;ASS_EQ(1+(2+3),(1+2)+3);<br/>
}<br/>
</tt></code>
To execute tests do the following:

<ul>
	<li><b>vtest</b>	to run all tests</li>
	<li><b>vtest -l</b> to list all test IDs</li>
	<li><b>vtest test1</b> to run only test1</li>
</ul>
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

  /** Returns the test unit with the given id, if it exists or NULL otherwise. */
  TestUnit* get(const char* unitId);

  /** Runs all tests of all existing test units
   *
   * returns true iff all tests were successfull.
   */
  bool runAllTests(ostream& out);
  void printTestNames(ostream& out);

  void add(TestUnit* tu)
  { TestUnitList::push(tu, _units); }

  /** Runs all tests of the given test unit. 
   *
   * returns true iff all tests of the unit were successfull.
   */
  bool runUnit(TestUnit* unit, ostream& out);

private:
  UnitTesting();
  ~UnitTesting();


  /** Runs a test as a single process and awaits its termination.
   * This is to provide isolation when running multiple tests in one go.
   *
   *  returns true iff the test process exited with status code 0
   */
  bool spawnTest(TestProc proc);

  TestUnitList* _units;
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


#define UT_CREATE Test::TestUnit UT_AUX_NAME(UT_AUX_NAME_STR)

// #define TEST_FUN_MULTI_PER_LINE(name, id_in_line)   \
//   void name(); \
//   Test::TU_Aux_Test_Adder _ut_aux_adder_##ID##_##LINE##_##id_in_line(UT_AUX_NAME,name,#name); \
//   void name()

#define TEST_FUN(name)  void name(); \
			Test::TU_Aux_Test_Adder UT_AUX_ADDER_NAME(name)(UT_AUX_NAME,name,#name); \
			void name()

}

#endif // __RuntimeStatistics__
