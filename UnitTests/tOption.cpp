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
        [](int i) -> std::string { return "some integer"; },
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
  std::string str ("some string");
  auto opt = Option<std::string&>(str);
  auto opt2 = Option<std::string>("some string");
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


struct MovableInt {
  int _value;
  MovableInt(int v) : _value(v) {}

  MovableInt(MovableInt const& other) 
    : _value(other._value) 
  {  }

  MovableInt& operator=(MovableInt const& other) 
  { _value = other._value; return *this; }


  MovableInt(MovableInt&& other) 
    : _value(other._value) 
  { other._value = -1; }

  MovableInt& operator=(MovableInt&& other) 
  { 
    _value = other._value;
    other._value = -1; 
    return *this;
  }

  friend std::ostream& operator<<(std::ostream& out, MovableInt const& self)
  { return out << self._value; }
};

TEST_FUN(ref_option_test_1) {
  auto val = MovableInt(42);
  auto opt1 = Option<MovableInt const&>(val);
  ASS(opt1.isSome())
  ASS_EQ(opt1->_value, 42)
  ASS_EQ(val._value, 42)

  auto opt2 = std::move(opt1);
  ASS(opt2.isSome())
  ASS_EQ(opt2->_value, 42)
  ASS_EQ(val._value, 42)

  auto opt_opt = some(std::move(opt2));
  auto opt3 = opt_opt.flatten();
  ASS(opt3.isSome())
  ASS_EQ(opt3->_value, 42)
  ASS_EQ(val._value, 42)
}



TEST_FUN(ref_option_test_2) {
  auto val = MovableInt(42);
  auto createOption = [&]() {
    return Option<MovableInt const&>(val);
  };
  auto res = createOption()
    .map([](auto x) {
        return x._value + 2000;
    });
  ASS_EQ(res, some(2042))
  ASS_EQ(val._value, 42)
}


