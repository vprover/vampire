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
#include "Inferences/ALASCA/InequalityFactoring.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Test/GenerationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                  \
  NUMBER_SUGAR(Num)                                                                                 \
  DECL_DEFAULT_VARS                                                                                 \
  DECL_VAR(x0,0)                                                                                    \
  DECL_VAR(x1,1)                                                                                    \
  DECL_VAR(x2,2)                                                                                    \
  DECL_VAR(x3,3)                                                                                    \
  DECL_VAR(x4,4)                                                                                    \
  DECL_CONST(a, Num)                                                                                \
  DECL_CONST(b, Num)                                                                                \
  DECL_CONST(c, Num)                                                                                \
  DECL_FUNC(f, {Num}, Num)                                                                          \
  DECL_FUNC(ff, {Num}, Num)                                                                         \
  DECL_FUNC(fff, {Num}, Num)                                                                        \
  DECL_FUNC(g, {Num, Num}, Num)                                                                     \
  DECL_FUNC(g0, {Num, Num}, Num)                                                                    \
  DECL_FUNC(g1, {Num, Num}, Num)                                                                    \
  DECL_PRED(r, {Num,Num})                                                                           \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

auto testInequalityFactoring(Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)
{ 
  auto s = testAlascaState(uwa);
  return alascaSimplRule(s,InequalityFactoring(s), ALASCA::Normalization(s)); 
}

template<class A> A* heap(A&& a) { return new A(std::move(a)); }

REGISTER_GEN_TESTER(AlascaGenerationTester<InequalityFactoring>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic00a,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( 3 * f(x) + y > 0 ), selected(4 * f(x) + z > 0)   }) })
      .expected(exactly(
            clause({ 4 * y + -3 * z > 0,  4 * f(x) + z > 0   })
          , clause({ 3 * z + -4 * y > 0,  3 * f(x) + y > 0   })
      ))
    )

TEST_GENERATION(basic00b,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( -3 * f(x) + y > 0 ), selected(4 * f(x) + z > 0)   }) })
      .expected(exactly(
        // nothing we only factor positive with positive
      ))
    )

TEST_GENERATION(basic00c,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( -3 * f(x) + y > 0 ), selected(-4 * f(x) + z > 0)   }) })
      .expected(exactly(
        // nothing we only factor positive with positive
      ))
    )

TEST_GENERATION(basic00d,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(  3 * f(x) + y > 0 ), selected(-4 * f(x) + z > 0)   }) })
      .expected(exactly(
        // nothing we only factor positive with positive
      ))
    )


TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(f(a) + a > 0), selected(f(x) + b > 0)   }) })
      .expected(exactly(
            clause({          f(a) + b > 0 , a - b > 0             })
          , clause({          f(a) + a > 0 , b - a > 0             })
      ))
    )

TEST_GENERATION(basic02b,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(f(a) + y > 0), selected(f(x) + z > 0)   }) })
      .expected(exactly(
            clause({          f(a) + y > 0 , z - y > 0            })
          , clause({          f(a) + z > 0 , y - z > 0            })
      ))
    )

TEST_GENERATION(basic03_symmetry_breaking,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(  f(a) > 0)  , selected(  f(a) > 0)  }) })
      .expected(exactly(
            clause({  f(a) > 0, num(0) > 0  })
          // , clause({  f(a) > 0, num(0) > 0  })
      ))
    )

TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected(  -f(a) > 0)  , selected(  f(a) > 0)  }) })
      .expected(exactly(
      ))
    )

TEST_GENERATION(uwa1,
    Generation::SymmetricTest()
      .rule(move_to_heap(testInequalityFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .inputs  ({  clause({selected(  f(a + b + x) > 0)  , selected(f(y + a) > 0)  }) })
      .expected(exactly(
            clause({  f(a + b + x) > 0, num(0) > 0, a + b + x != y + a  })
          , clause({  f(y + a) > 0    , num(0) > 0, a + b + x != y + a  })
      ))
    )

TEST_GENERATION(uwa2,
    Generation::SymmetricTest()
      .rule(move_to_heap(testInequalityFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .inputs  ({  clause({selected(  f(2 * x) > 0)  , selected(f(x + 1) > 0)  }) })
      .expected(exactly(
            clause({  f(2 * x) > 0, num(0) > 0, 2 * x != x + 1  })
          , clause({  f(x + 1) > 0, num(0) > 0, 2 * x != x + 1  })
      ))
    )

TEST_GENERATION(uwa3,
    Generation::SymmetricTest()
      .rule(move_to_heap(testInequalityFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
      .inputs  ({  clause({selected(  f(2 * x) > 0)  , selected(f(x) > 0)  }) })
      .expected(exactly(
            clause({  f(2 * x) > 0, num(0) > 0, 2 * x != x  })
          , clause({  f(    x) > 0, num(0) > 0, 2 * x != x  })
      ))
    )

// TODO think about this test case again
// TEST_GENERATION(misc1,
//     Generation::SymmetricTest()
//       .rule(move_to_heap(testInequalityFactoring(Shell::Options::UnificationWithAbstraction::ALASCA_ONE_INTERP)))
//       .inputs  ({  clause({ selected( f(x) + f(y) > 0 )  , selected( f(y) + f(x) > 0 )  }) })
//       .expected(exactly( 
//             clause({ f(x) + f(y) > 0, -f(y) + f(y) > 0 }), clause({ f(x) + f(y) > 0, -f(y) + f(y) > 0 })
//           , clause({ f(x) + f(y) > 0, -f(x) + f(x) > 0 }), clause({ f(x) + f(y) > 0, -f(x) + f(x) > 0 })
//       ))
//     )

TEST_GENERATION(max_s1_after_unif_1,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( f(x) + ff(y) > 0 )  , selected( f(y) + ff(x) > 0 )  }) })
      .expected(exactly( 
            clause({ f(x) + ff(x) > 0, -f(x) + f(x) > 0 }), clause({ f(x) + ff(x) > 0, -f(x) + f(x) > 0 })
      ))
    )

TEST_GENERATION(max_s2_after_unif_1,
    Generation::SymmetricTest()
      .inputs  ({  clause({  selected( f(y) + ff(x) > 0 ), selected( f(x) + ff(y) > 0 )    }) })
      .expected(exactly( 
            clause({ f(x) + ff(x) > 0, -f(x) + f(x) > 0 }), clause({ f(x) + ff(x) > 0, -f(x) + f(x) > 0 })
      ))
    )

TEST_GENERATION(max_s1_after_unif_2,
    Generation::SymmetricTest()
      .inputs  ({  clause({  selected( ff(y) + fff(x) > 0 ), selected( f(z) + fff(y) > 0 )    }) })
      .expected(exactly( 
            clause({ ff(x) + fff(x) > 0, f(z) - ff(x) > 0 })
          , clause({ f(z)  + fff(x) > 0, ff(x) - f(z) > 0 })
      ))
    )

/////////////////////////////////////////////
// ALASCA VERSION
///////////////////////////////

TEST_GENERATION(alasca01,
    Generation::SymmetricTest()
      .inputs  ({  clause({  selected( ff(a) + f(y) > 0 ), selected( ff(x) + f(z) > 0 )   }) })
      .expected(exactly(
            clause({         ff(a) + f(y) > 0 , f(z) - f(y) > 0        })
          , clause({         ff(a) + f(z) > 0 , f(y) - f(z) > 0        })

          , clause({         ff(a) + f(y) > 0 , ff(x) - ff(a) > 0        })
          , clause({         ff(x) + f(y) > 0 , ff(a) - ff(x) > 0        })
      ))
    )

TEST_GENERATION(alasca02,
    Generation::SymmetricTest()
      .inputs  ({  clause({  selected( 2 * ff(a) + f(y) > 0 ), selected( 3 * ff(x) + f(z) > 0 )   }) })
      .expected(exactly(
            clause({         2 * ff(a) + f(y) > 0 , -3 * f(y) + 2 * f(z) > 0        })
          , clause({         3 * ff(a) + f(z) > 0 , -2 * f(z) + 3 * f(y) > 0        })

          , clause({         2 * ff(a) + f(y) > 0 , -2 * ff(a) + 3 * ff(x) > 0        })
          , clause({         3 * ff(x) + f(y) > 0 , -3 * ff(x) + 2 * ff(a) > 0        })
      ))
    )

TEST_GENERATION(alasca_bug1,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( f(x) + y > 0 ), selected( f(x) + z > 0 ) }) })
      .expected(exactly(
            clause({         f(x) + y > 0 , z - y > 0        })
          , clause({         f(x) + z > 0 , y - z > 0        })
      ))
    )

TEST_GENERATION(alasca_bug2,
    Generation::SymmetricTest()
      .inputs  ({  clause({ selected( f(x) + y + 1 > 0 ), selected( f(x) + z > 0 ) }) })
      .expected(exactly(
            clause({         f(x) + y + 1 > 0 , z     - y + -1 > 0 })
          , clause({         f(x) + z     > 0 , y + 1 - z      > 0 })
      ))
    )

TEST_GENERATION(alasca_bug3,
    Generation::SymmetricTest()
      .inputs  ({  clause({  selected(a + x + -1 > 0), selected(a + -x > 0) }) })
      .expected(exactly(
            clause({         a +  x + -1 > 0, (-x) + (-x + 1) > 0 })
          , clause({         a + -x      > 0, (x + -1) +  (x) > 0 })
      ))
                            // if (!_alascaFactoring && isSelected(j))
    )

  // f(x) + y <= 0 <=> -f(x) - y >= 0

// testing different symbols
TEST_GENERATION(check_symbols_01,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a > 0 ), selected(f(x) + b > 0)   }) })
      .expected(exactly(
            clause({ a - b > 0, f(x) + b > 0   })
          , clause({ b - a > 0, f(x) + a > 0   })
      ))
    )
TEST_GENERATION(check_symbols_02,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a > 0 ), selected(f(x) + b >= 0)   }) })
      .expected(exactly(
            clause({ a - b >  0, f(x) + b >= 0   })
          , clause({ b - a >= 0, f(x) + a >  0   })
      ))
    )
TEST_GENERATION(check_symbols_03,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a >= 0 ), selected(f(x) + b > 0)   }) })
      .expected(exactly(
            clause({ a - b >= 0, f(x) + b >  0   })
          , clause({ b - a >  0, f(x) + a >= 0   })
      ))
    )
TEST_GENERATION(check_symbols_04,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a >= 0 ), selected(f(x) + b >= 0)   }) })
      .expected(exactly(
            clause({ a - b > 0, f(x) + b >= 0   })
          , clause({ b - a > 0, f(x) + a >= 0   })
      ))
    )


TEST_GENERATION(check_symbols_05,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a == 0 ), selected(f(x) + b >= 0)   }) })
      .expected(exactly(
        // we don't use this rule for equality
      ))
    )
TEST_GENERATION(check_symbols_06,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a != 0 ), selected(f(x) + b >= 0)   }) })
      .expected(exactly(
        // we don't use this rule for equality
      ))
    )
TEST_GENERATION(check_symbols_07,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a > 0 ), selected(f(x) + b != 0)   }) })
      .expected(exactly(
        // we don't use this rule for equality
      ))
    )

TEST_GENERATION(check_symbols_08,
    Generation::SymmetricTest()
      .inputs  ({  clause({selected( f(x) + a != 0 ), selected(f(x) + b != 0)   }) })
      .expected(exactly(
        // we don't use this rule for equality
      ))
    )
