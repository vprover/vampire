#include "Lib/Coproduct.hpp"
#include "Test/UnitTesting.hpp"


#define UNIT_ID Coproduct
UT_CREATE;

using namespace Kernel;
using namespace Lib;

TEST_FUN(is_variant_01) {
  auto x = Coproduct<int, int, const char*>::variant<2>("lala");
  ASS(!x.is<0>())
  ASS(!x.is<1>())
  ASS(x.is<2>())
  // x.is<4>() // <- does not compile
}

TEST_FUN(equal_02) {
  auto x = Coproduct<int, int, float>::variant<0>(0);
  auto y = Coproduct<int, int, float>::variant<1>(0);
  ASS(x != y)
}

TEST_FUN(equal_03) {
  auto x = Coproduct<int, int, float>::variant<0>(0);
  auto y = Coproduct<int, int, float>::variant<0>(0);
  ASS(x == y)
}

TEST_FUN(equal_04) {
  auto x = Coproduct<int, int, float>::variant<0>(0);
  auto y = Coproduct<int, int, float>::variant<0>(1);
  ASS(x != y)
}

TEST_FUN(unwrap_01) {
  auto x = Coproduct<int, int, float>::variant<0>(0);
  auto y = Coproduct<int, int, float>::variant<1>(0);
  ASS(x.unwrap<0>() == y.unwrap<1>());
}


TEST_FUN(unwrap_02) {
  auto x = Coproduct<int, int, float>::variant<0>(0);
  auto y = Coproduct<int, int, float>::variant<1>(1);
  ASS(x.unwrap<0>() != y.unwrap<1>());
}


struct NonCopy {
  bool content;
  bool wasMoved;
  NonCopy(bool content) : content(content), wasMoved(false) {}
  NonCopy(NonCopy&& other) 
    : content(other.content)
    , wasMoved(false)  {
    other.wasMoved = true;
  }
  NonCopy& operator=(NonCopy&& other) {
    content = other.content;
    other.wasMoved = true;
    return *this;
  }

  bool operator==(const NonCopy& other) const {
    return content == other.content;
  }
  friend ostream& operator<<(ostream& out, const NonCopy& x)  {
    return out << "NonCopy(" << x.content << ")";
  }
};

TEST_FUN(move_01) {

  auto y = Coproduct<int, NonCopy>::variant<1>(NonCopy( true ));

  ASS((y == Coproduct<int,NonCopy>::variant<1>(NonCopy( true ))));
  ASS((y != Coproduct<int,NonCopy>::variant<1>(NonCopy( false ))));
  ASS((y != Coproduct<int,NonCopy>::variant<0>(1)));

  y = Coproduct<int, NonCopy>::variant<0>(1);

  ASS((y == Coproduct<int,NonCopy>::variant<0>(1)));
  ASS((y != Coproduct<int,NonCopy>::variant<1>(NonCopy( false ))));
  ASS((y != Coproduct<int,NonCopy>::variant<0>(0)));
}

// TEST_FUN(move_02) {
//
//   auto x = Coproduct<int, NonCopy>::variant<1>(NonCopy( true ));
//
//   auto y = x;
//
//   ASS(!x.unwrap<NonCopy>().wasMoved)
//   ASS(!y.unwrap<NonCopy>().wasMoved)
//
// }
