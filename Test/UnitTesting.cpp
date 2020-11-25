
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

namespace Test {

using namespace Lib;
using namespace Lib::Sys;

TestUnit::TestUnit()
: _tests()
{ }

TestUnit TestUnit::_instance;
TestUnit& TestUnit::instance() 
{ return _instance; }

bool TestUnit::run(ostream& out)
{
  Stack<Test>::BottomFirstIterator uit(_tests);

  if(!uit.hasNext()) {
    out<<"No tests to run."<<endl;
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

void TestUnit::add(Test t)
{ _tests.push(t); }


/**
 * Run test in a different process and wait for its termination
 * This is to provide isolation when running multiple tests in one go.
 *
 * returns true iff the test process exited with status code 0
 */
bool TestUnit::spawnTest(TestProc proc)
{
  auto mp = Multiprocessing::instance();
  pid_t fres = mp->fork();
  if(fres == 0) {
    proc();
    _exit(0); // don't call parent's atexit! 
  } else {
    int childRes;
    Multiprocessing::instance()->waitForParticularChildTermination(fres, childRes);
    return  childRes == 0;
  }
}

} // namespace Test

int main() {
  bool success = Test::TestUnit::instance().run(std::cout);
  return success ? 0 : -1;
}


