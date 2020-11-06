#include "Lib/Option.hpp"

#include "Test/UnitTesting.hpp"


#define UNIT_ID Option
UT_CREATE;

using namespace Kernel;
using namespace Lib;

class LeaqueChecker 
{
  bool _moved;
public:
  static int instances;
  static int deletes;

  LeaqueChecker(LeaqueChecker const& o) : _moved(o._moved) { if (!_moved) { instances++; }     }
  LeaqueChecker(LeaqueChecker     && o) : _moved(o._moved) { o._moved = true; }
  LeaqueChecker& operator=(LeaqueChecker && o) 
  {
    if (!_moved && !o._moved) {
      deletes++;
    }
    _moved = o._moved;
    o._moved = true;
    return *this; 
  }
  LeaqueChecker& operator=(LeaqueChecker const& o) 
  { 
    _moved = o._moved;
    return *this; 
  }
  LeaqueChecker()  { instances++; }
  ~LeaqueChecker() { if (!_moved) deletes++;   }
};

int LeaqueChecker::deletes   = 0;
int LeaqueChecker::instances = 0;

TEST_FUN(test_LeaqueChecker_1) {

  using Opt = Option<LeaqueChecker>;
  {
    auto t1 = Opt(LeaqueChecker());
    LeaqueChecker t2;
    t2 = t1.unwrap();
  }

  ASS_EQ(LeaqueChecker::instances, LeaqueChecker::deletes)
}


TEST_FUN(test_LeaqueChecker_2) {

  using Opt = Option<LeaqueChecker>;
  {
    auto t1 = Opt(LeaqueChecker());
    t1.unwrap() = LeaqueChecker();
  }

  ASS_EQ(LeaqueChecker::instances, LeaqueChecker::deletes)
}


