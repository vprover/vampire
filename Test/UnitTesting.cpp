
/*
 * File UnitTesting.cpp.
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
 * @file RuntimeStatistics.cpp
 * Implements class RuntimeStatistics.
 */

#include <iomanip>
#include "Debug/Tracer.hpp"

#include "Lib/Sys/Multiprocessing.hpp"

#include "Lib/Comparison.hpp"
#include "Lib/Int.hpp"
#include "Lib/Sort.hpp"
#include "Lib/Stack.hpp"

#include "UnitTesting.hpp"

namespace Test
{

using namespace Lib;
using namespace Lib::Sys;

TestUnit::TestUnit(const char* id)
: _id(id), _tests(0)
{
  CALL("TestUnit::TestUnit");

  UnitTesting::instance()->add(this);
}


/**
 * Return iterator over the tests in this unit
 *
 * All elements of the iterator must be retrieved, or
 * a memory leak will occur
 */
TestUnit::Iterator TestUnit::getTests()
{
  CALL("TestUnit::getTests");

  TestList* lst = TestList::reverse(TestList::copy(_tests));
  return TestList::DestructiveIterator(lst);
}


UnitTesting* UnitTesting::instance()
{
  static UnitTesting inst;

  return &inst;
}

UnitTesting::UnitTesting()
: _units(0)
{
}

UnitTesting::~UnitTesting()
{
  TestUnitList::destroy(_units);
}

TestUnit* UnitTesting::get(const char* unitId)
{
  CALL("UnitTesting::get");

  TestUnitList::Iterator it(_units);
  while(it.hasNext()) {
    TestUnit* u=it.next();
    if(!strcmp(u->id(), unitId)) {
      return u;
    }
  }
  return 0;
}

// TestUnit* UnitTesting::getUnit(const char* unitId)
// {
//   TestUnit* unit=get(unitId);
//   if(!unit) {
//     return false;
//   }
//   runUnit(unit, out);
//   return true;
// }

bool UnitTesting::runUnit(TestUnit* unit, ostream& out)
{
  out<<"Testing unit "<<unit->id()<<":"<<endl;

  TestUnit::Iterator uit=unit->getTests();
  if(!uit.hasNext()) {
    out<<"No tests in this unit"<<endl;
  }
  unsigned cnt_fail = 0;
  unsigned cnt_ok  = 0;
  while(uit.hasNext()) {
    TestUnit::Test t=uit.next();
    out << "Running " << t.name << "... ";
    out.flush();
    bool ok;
    {
      CALL(t.name);
      ok = spawnTest(t.proc);
    }
    out << "\r" << ( ok ? "[  OK  ]" : "[ FAIL ]" ) << " " << t.name << "          " << endl;
    if (ok) cnt_ok++;
    else cnt_fail++;
  }
  out << endl;
  auto cnt = cnt_fail + cnt_ok;
  out << fixed << setprecision(1);
  out << "Tests run: " << cnt << endl;
  out << "  - ok   " << cnt_ok   << "\t(" << (cnt_ok   * 100.0 / cnt) << ") %" << endl;
  out << "  - fail " << cnt_fail << "\t(" << (cnt_fail * 100.0 / cnt) << ") %" << endl;
  return cnt_fail == 0;
}

/**
 * Run test in a different process and wait for its termination
 * This is to provide isolation when running multiple tests in one go.
 *
 * returns true iff the test process exited with status code 0
 */
bool UnitTesting::spawnTest(TestProc proc)
{

  auto mp = Multiprocessing::instance();
  pid_t fres = mp->fork();
  if(!fres) {
    proc();
    _exit(0); // don't call parent's atexit! 
  } else {
    int childRes;
    Multiprocessing::instance()->waitForParticularChildTermination(fres, childRes);
    return  childRes == 0;
  }
}

bool UnitTesting::runAllTests(ostream& out)
{
  TestUnitList::Iterator tuit(_units);
  bool allOk = true;
  while(tuit.hasNext()) {
    allOk &= runUnit(tuit.next(), out);
    if(tuit.hasNext()) {
      out<<endl;
    }
  }
  return allOk;
}

void UnitTesting::printTestNames(ostream& out)
{
  CALL("UnitTesting::printTestNames");

  TestUnitList::Iterator tuit(_units);
  while(tuit.hasNext()) {
    out<<tuit.next()->id()<<endl;
  }
}


}

