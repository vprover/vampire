/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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

namespace Test {

using namespace Lib;

typedef void (*TestProc)();

class TestUnit
{
public:
  TestUnit(std::string const&);

  struct Test
  {
    Test() {}
    Test(TestProc proc, const char* name) : proc(proc), name(name) {}

    TestProc proc;
    const char* name;
  };


  void add(Test);

  /** Runs all tests of this TestUnit
   *
   * returns true iff all tests of the unit were successfull.
   */
  bool run(std::ostream& out);
  bool runTestsWithNameSubstring(std::string const& pref, std::ostream& out);
  bool runTest(std::string const& name);


  bool hasTest(std::string const& name);

  friend std::ostream& operator<<(std::ostream& out, TestUnit const& t)
  { return out << t._name << t._tests; }

  std::string const& id() const { return _name; }

  Stack<Test> const& tests() { return _tests; }
private:
  Test* findTest(std::string const& testCase);
  /** Runs a test as a single process and awaits its termination.
   * This is to provide isolation when running multiple tests in one go.
   *
   *  returns true iff the test process exited with status code 0
   */
  bool spawnTest(TestProc proc);

  // TODO replace by Map as soon as integer-arithmetic PR with Map additions has landed
  Stack<Test> _tests;
  std::string _name;
};

/** Main class for running tests */
class UnitTesting 
{
  static UnitTesting* _instance;
  Stack<TestUnit> _units;
  UnitTesting() : _units() {}
public:
  static UnitTesting& instance();

  bool add(std::string const& testUnit, TestUnit::Test test);
  TestUnit* findUnit(std::string const& id);
  bool listTests(Stack<std::string>const& args);
  bool run(Stack<std::string>const& args);
  bool runUnit(std::string const& args);
  bool runTest(std::string const& unit, std::string const& testCase);
};

std::ostream& operator<<(std::ostream& out, TestUnit::Test const& t);

class TestAdder
{
public:
  TestAdder(const char* unit, TestProc proc, const char* name);
};

#define EXPAND(a) a
#define _CAT(a,b) a ## b
#define CAT(a,b) EXPAND(_CAT(a,b)) // expands arguments before concattentation
#define __TEST_ADDER(name)   CAT(CAT(CAT(__addTest__, UNIT_ID), __), name)
#define __TEST_FN_NAME(name) CAT(CAT(CAT(__testFn__ , UNIT_ID), __), name)

#define TEST_FUN(name)                                                                                        \
    void __TEST_FN_NAME(name)();                                                                              \
    Test::TestAdder __TEST_ADDER(name)(UNIT_ID_STR, __TEST_FN_NAME(name), #name);                             \
    void __TEST_FN_NAME(name)()

} // namespace Test

int main(int argc, const char** argv);

#endif // __UnitTesting__
