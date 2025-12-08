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
#include "Inferences/ALASCA/Coherence.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/GenerationTester.hpp"
#include "Test/AlascaTestUtils.hpp"
#include "Inferences/ALASCA/Coherence.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::ALASCA;

#define SUGAR(Num)                                                                        \
  NUMBER_SUGAR(Num)                                                                       \
                                                                                          \
  DECL_DEFAULT_VARS                                                                       \
                                                                                          \
  DECL_FUNC(f, {Num}, Num)                                                                \
  DECL_FUNC(f2, {Num,Num}, Num)                                                           \
  DECL_FUNC(g, {Num}, Num)                                                                \
  DECL_FUNC(h, {Num}, Num)                                                                \
                                                                                          \
  DECL_CONST(a, Num)                                                                      \
  DECL_CONST(b, Num)                                                                      \
  DECL_CONST(c, Num)                                                                      \
                                                                                          \
  DECL_PRED(p, {Num})                                                                     \
  DECL_PRED(r, {Num,Num})                                                                 \
                                                                                          \
  auto isInteger = [&](auto t) { return t == floor(t); };                                 \


#define MY_SYNTAX_SUGAR SUGAR(Real)

#define UWA_MODE Options::UnificationWithAbstraction::ALASCA_MAIN

inline Generation::TestIndices alascaCoherenceIndices()
{ return {
    [](const SaturationAlgorithm&){ return new AlascaIndex<CoherenceConf<RealTraits>::Lhs>();},
    [](const SaturationAlgorithm&){ return new AlascaIndex<CoherenceConf<RealTraits>::Rhs>();},
  }; }

REGISTER_GEN_TESTER(AlascaGenerationTester<Coherence<RealTraits>>())

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(a + b)) )  }) })
      .expected(exactly(
            clause({ p(a + b)  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(2 * a + b)) )  }) })
      .expected(exactly(
            clause({ p(a + b + floor(a))  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(     p(floor(2 * a + b)) )  }) })
      .expected(exactly(
            clause({ p(a + b + floor(a))  })
      ))
    )


TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(     p(floor(2 * a + 2 * b)) )  }) })
      .expected(exactly(
            clause({ p(2 * a + 2 * b)  })
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( 2 * a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(a + b)) )  }) })
      .expected(exactly(
          clause({ p(2 * a + b + floor(-a)) })
      ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( f(x) + f(y) == floor(f2(x,y)) )  }) 
                , clause({ selected(     p(floor(f(a) + f(b))) )  }) })
      .expected(withoutDuplicates(exactly(
              clause({ p(f(a) + f(x) + floor(f(b) - f(x)))  })
            , clause({ p(f(b) + f(x) + floor(f(a) - f(x)))  })
      )))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected(  isInteger(f(x)) )  }) 
                , clause({ selected(     p(floor(f(a) + f(b))) )  }) })
      .expected(exactly(
              clause({ p(f(a) + floor(f(b)))  })
            , clause({ p(f(b) + floor(f(a)))  })
      ))
    )


TEST_GENERATION(basic08,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(p(floor(-a + -b)) )  }) })
      .expected(exactly(
          clause({ p(-a + -b) })
      ))
    )

TEST_GENERATION(basic08minus,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(-a + -b) )  }) 
                , clause({ selected(p(floor(-a + -b)) )  }) })
      .expected(exactly(
          clause({ p(-a + -b) })
      ))
    )

TEST_GENERATION(factors_0,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(a + b + c)) )  }) })
      .expected(exactly(
          clause({ p(a + b + c) })
      ))
    )

TEST_GENERATION(factors_1,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + -c)) )  }) })
      .expected(exactly(
          clause({ p(-a + -b + -c) })
      ))
    )

TEST_GENERATION(factors_2,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + b + -c)) )  }) })
      .expected(exactly(
          clause({ p(-c - b - a + floor(2 * b)) })
      ))
    )

TEST_GENERATION(factors_3,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + 2 * c)) )  }) })
      .expected(exactly(
          clause({ p(2 * (a + b + c) + floor(-3 * a + -3 * b)) })
      ))
    )

TEST_GENERATION(factors_4,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + -2 * c)) )  }) })
      .expected(exactly(
          clause({ p(-2 * a + -2 * b + -2 * c + floor(a + b)) })
      ))
    )

TEST_GENERATION(factors_5,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(a + b + 2 * c)) )  }) })
      .expected(exactly(
          clause({ p(2 * a + 2 * b + 2 * c + floor(-a + -b)) })
      ))
    )

// TODO check theory whether we really should do this with factors != +-1
TEST_GENERATION(factors_6,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(2 * a + 4 * b + 2 * c)) )  }) })
      .expected(exactly(
          clause({ p(2 * a + 2 * b + 2 * c + floor(2 * b)) })
      ))
    )

TEST_GENERATION(factors_7,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(frac(1,2) * a + 4 * b + 2 * c)) )  }) })
      .expected(exactly(
          clause({ p(2 * (a + b + c) + floor((frac(1,2) - 2) * a + 2 * b)) })
      ))
    )

TEST_GENERATION(vars_0,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(a + f(b))) )  }) })
      .expected(exactly(
          clause({ p(f(b) + b + floor(a - b)) })
      ))
    )

TEST_GENERATION(vars_1,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(a + f(a))) )  }) })
      .expected(exactly(
                  clause({          p(      a + f(a))     })
      ))
    )

TEST_GENERATION(vars_2,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(2 * a + f(a))) )  }) })
      .expected(exactly(
                  clause({          p(floor(a) + a + f(a))     })
      ))
    )

TEST_GENERATION(vars_3,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(y) + g(x)) )  }) 
                , clause({ selected(p(floor(a + f(a) + g(b))) )  }) })
      .expected(exactly(
            clause({ p(f(a) + x + g(x) + floor(a - x + g(b) - g(x))) })
          , clause({ p(g(b) + b + f(x) + floor(a + f(a) - b - f(x)) ) })
      ))
    )

TEST_GENERATION(vars_4,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(y) + g(x)) )  }) 
                , clause({ selected(p(floor(a + f(b) + g(a))) )  }) })
      .expected(exactly(
                  clause({ p(x + f(b) + g(x) + floor(a + g(a) - g(x) - x)) })
                , clause({ p(a + f(y) + g(a) + floor(f(b) - f(y))) })
      ))
    )

TEST_GENERATION(vars_5,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(b + f(b))) )  }) })
      .expected(exactly(
                  clause({          p(b + f(b))     })
      ))
    )

TEST_GENERATION(vars_6,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(y + g(y))) )  }) })
      .expected(exactly(
      ))
    )

TEST_GENERATION(vars_7,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(a + b + f(a + b))) )  }) })
      .expected(exactly(
                   clause({ p(a + b + f(a + b))  }) 
      ))
    )

TEST_GENERATION(vars_8,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(a + 2 * b + f(a + b))) )  }) })
      .expected(exactly(
                   clause({ p(a + b + f(a + b) + floor(b)) }) 
      ))
    )

TEST_GENERATION(vars_9,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(a + f(y))) )  }) })
      .expected( exactly(
        clause({ p(f(x) + x + floor(a - x)) })
      ))
    )

TEST_GENERATION(vars_10,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(y)) )  }) 
                , clause({ selected(p(floor(a + b)) )  }) })
      .expected( exactly(
          /* nothing. these cases are to be handled by an abstraction rule */ 
      ))
    )

  // TODO coherence needs to be applied for numerals as well but this can be done in normalization!!
TEST_GENERATION(numeral_0,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( floor(a) == 0 )  }) 
                 , clause({ selected(p(floor(b + frac(1,6))) )  }) })
      .expected(exactly(/* nothing */))
    )

TEST_GENERATION(numeral_1,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( floor(a) == frac(1,2) )  }) 
                 , clause({ selected(p(floor(b + frac(1,6))) )  }) })
      .expected(exactly(/* nothing */))
    )


TEST_GENERATION(bug01,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ isInteger(f2(x,y) + 0)  }) 
                 , clause({  0 != (x + y + -f2(y,x) + -floor(x + y + -f2(y,x))) /*, 0 == (x + y + -f2(y,x))*/ }) 
                 })
      .expected(exactly(
                   clause({  0 != (x + y + -floor(x + y)) /*, 0 == (x + y + -f2(y,x))*/ })
          /* nothing */))
    )

TEST_GENERATION(bug02,
    Generation::SymmetricTest()
      .indices(alascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ isInteger(f2(x,y) + 0)  }) 
                 , clause({  
                       0 != (x + y + -f2(y,x) + -floor(x + y + -f2(y,x))) 
                     , 0 == (x + y + -f2(y,x))
                       }) })
      .expected(exactly(
          clause({ 0 != (x + y - floor(x + y)) 
                 , 0 == (x + y + -f2(y,x))     })
          ))
    )
