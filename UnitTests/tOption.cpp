/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Lib/Option.hpp"

#include "Test/UnitTesting.hpp"

using namespace Kernel;
using namespace Lib;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// USAGE EXAMPLES
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

TEST_FUN(examples__isNone) {
  auto opt = Option<int>();
  // with isNone/isSome we can check whether the option contains a value
  ASS( opt.isNone())
  ASS(!opt.isSome())
}

TEST_FUN(examples__isSome) {
  auto opt = Option<int>(1);
  // with isNone/isSome we can check whether the option contains a value
  ASS( opt.isSome())
  ASS(!opt.isNone())
  // with unwrap we can get the value
  ASS_EQ(opt.unwrap(), 1)
}

TEST_FUN(examples__match) {
  // we can also match on Options instead of testing with isSome and unwrap
  auto opt = Option<int>();
  auto result = opt.match(
        [](int i) -> vstring { return "some integer"; },
        [](     )            { return "nothing";      }
        );
  ASS_EQ("nothing", result)
}


TEST_FUN(examples__unwrapOrElse) {
  // unwrapOrElse yields the option's value if there is one, or returns a fallback value created with a closure otherwise
  ASS_EQ(1, Option<int>(1).unwrapOrElse([]() { return 2; }));
  ASS_EQ(2, Option<int>().unwrapOrElse([]() { return 2; }));
}


TEST_FUN(examples__unwrapOrInit) {
  // unwrapOrInit does the same thing as unwrapOrElse, but initializes the Option with the fallback value 
  auto opt = Option<int>();
  ASS_EQ(2, opt.unwrapOrInit([]() { return 2; }));
  ASS_EQ(2, opt.unwrap());
}


TEST_FUN(examples__toOwned) {
  // an option of a reference type can be turned into an option of the corresponding value, by coping it:
  vstring str ("lala");
  auto opt = Option<vstring&>(str);
  auto opt2 = Option<vstring>("lala");
  // ASS_NEQ(opt, opt2) // <- does not compile. different types!!
  ASS_EQ(opt.toOwned(), opt2);
}


TEST_FUN(examples__map) {
  // as well-known from function programming, Option (aka Maybe in haskell), is a Monad, hence a Functor. Therefore we can 
  // map it:
  auto opt = Option<int>(3);
  auto result = opt.map([](int i) -> double
      { return ((double)i) / 2; });

  ASS_EQ(result, Option<double>(1.5));
}


TEST_FUN(examples__andThen) {
  // and of course we can flatMap/(>>=)/andThen it as well
  auto opt = Option<int>(3);

  auto result = opt.andThen([](int i) -> Option<double> { 
      auto out = ((double)i) / 2.0; 
      if (out > 0.5) {
        return Option<double>();
      } else {
        return Option<double>(out);
      }
  });


  ASS_EQ(result, Option<double>());
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// MISC TESTS
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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
  LeaqueChecker() : _moved(false) { instances++; }
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


