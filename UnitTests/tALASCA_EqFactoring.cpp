/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/SyntaxSugar.hpp"
#include "Inferences/ALASCA/EqFactoring.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Test/GenerationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define INT_TESTS 0

#define SUGAR(Num)                                                                                  \
  NUMBER_SUGAR(Num)                                                                                 \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(g, {Num}, Num)                                                                          \
  DECL_FUNC(g2, {Num, Num}, Num)                                                                    \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_PRED(p, {Num})                                                                               \
  DECL_PRED(r, {Num,Num})                                                                           \
                                                                                                    \
  DECL_SORT(alpha)                                                                                  \
  DECL_FUNC(fa, {Num}, alpha)                                                                       \
  DECL_CONST(aa, alpha)                                                                             \
  DECL_CONST(ba, alpha)                                                                             \
  DECL_FUNC(fn, {alpha}, Num)                                                                       \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

REGISTER_GEN_TESTER(AlascaGenerationTester<EqFactoring>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////


TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(f(a) - c == 0), selected(f(a) - b == 0 ),  })  })
      .expected(exactly( clause({           b != c,                      f(a) - b == 0     })  ))
    )

TEST_GENERATION(basic02a,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(4 * f(a) - c == 0), selected( 3 * f(a) - b == 0 ),  }) })
      .expected(exactly( clause({           frac(1, 3) * b != frac(1,4) * c,  3 * f(a) - b == 0     }) ))
    )

TEST_GENERATION(basic02b,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(-4 * f(a) + c == 0), selected( 3 * f(a) - b == 0 ),  }) })
      .expected(exactly( clause({           frac(1, 3) * b != frac(1,4) * c,  3 * f(a) - b == 0     }) ))
    )

TEST_GENERATION(basic02c,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(-4 * f(a) + c == 0), selected( -3 * f(a) + b == 0 ),  }) })
      .expected(exactly( clause({           frac(1, 3) * b != frac(1,4) * c,  -3 * f(a) + b == 0     }) ))
    )

TEST_GENERATION(basic02d,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(-4 * f(a) - c == 0), selected( -3 * f(a) + b == 0 ),  }) })
      .expected(exactly( clause({           frac(1, 3) * b != frac(-1,4) * c,  -3 * f(a) + b == 0     }) ))
    )

TEST_GENERATION(basic02e,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(-4 * f(a) - c == 0), selected( 3 * f(a) + b == 0 ),  }) })
      .expected(exactly( clause({           frac(-1, 3) * b != frac(-1,4) * c,  3 * f(a) + b == 0     }) ))
    )

TEST_GENERATION(basic03_different_sorts_a,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(f(a) - c == 0), selected( f(a) + b == 0 ), selected( fa(f(a)) == aa )  }) })
      .expected(exactly( /* northing */ ))
    )

TEST_GENERATION(basic03_different_sorts_b,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(f(a) - c == 0), selected( f(a) + b == 0 ), selected( fa(f(a)) == aa ), selected( fa(f(a)) == ba )  }) })
      .expected(exactly( clause({               f(a) - c == 0,            f(a) + b == 0  ,           fa(f(a)) == aa  ,                ba != aa     }) ))
    )

TEST_GENERATION(basic03_different_sorts_c,
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(fn(fa(a)) - c == 0), selected( fn(fa(a)) - b == 0 ), selected( fa(a) == aa ), selected( fa(a) == ba )  }) })
      .expected(exactly( clause({                       b != c     ,           fn(fa(a)) - b == 0  ,           fa(a) == aa  ,           fa(a) == ba    }) ))
    )

TEST_GENERATION(basic03_different_sorts_d,
    Generation::SymmetricTest()
      .inputs  ({        clause({       selected( fn(fa(a)) - b == 0 ), selected( fa(a) == aa ), selected( fa(a) == ba )  }) })
      .expected(exactly( /* nothing */ ))
    )

TEST_GENERATION(unshielded_variables_01,
    Generation::SymmetricTest()
      .inputs  ({        clause({  x == aa, fa(b) == ba  }) })
      .expected(exactly( clause({ ba != aa, fa(b) == aa  })  )))

TEST_GENERATION(unshielded_variables_02,
    Generation::SymmetricTest()
      .inputs  ({        clause({ x - a == 0, f(b) - b == 0  }) })
      .expected(exactly( /* nothing */ )))

#if INT_TESTS
TEST_GENERATION_WITH_SUGAR(int_01, SUGAR(Int),
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(f(a) - c == 0), selected(f(a) - b == 0 ),  })  })
      .expected(exactly( clause({           b != c,                      f(a) - b == 0     })  ))
    )

TEST_GENERATION_WITH_SUGAR(int_02a, SUGAR(Int),
    Generation::SymmetricTest()
      .inputs  ({        clause({      selected(4 * f(a) - c == 0), selected( 3 * f(a) - b == 0 ),  }) })
      .expected(exactly( clause({           4 * b != 3 * c,  3 * f(a) - b == 0     }) ))
    )

#endif // INT_TESTS

TEST_GENERATION(two_var_01,
    Generation::SymmetricTest()
      .inputs  ({        clause({      x - a == 0, y == aa,  })  })
      .expected(exactly( /* nothing */ ))
    )


  // xa == ya \/ xn == yn
