/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/LASCA/Coherence.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp" 
#include "Inferences/PolynomialEvaluation.hpp"
#include "Test/LascaSimplRule.hpp"
#include "Inferences/LASCA/Coherence.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::LASCA;
#define INT_TESTS 0

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

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

#define UWA_MODE Options::UnificationWithAbstraction::LPAR_MAIN



inline std::shared_ptr<LascaState> state(Options::UnificationWithAbstraction uwa) 
{ 
  std::shared_ptr<LascaState> out = testLascaState(uwa, /* string norm */ false, /* ord */ nullptr, /* uwaFixedPointIteration */ true); 
  return out;
}

inline Stack<std::function<Indexing::Index*()>> lascaCoherenceIndices()
{ return {
    [](){ return new LascaIndex<CoherenceConf<RealTraits>::Lhs>();},
    [](){ return new LascaIndex<CoherenceConf<RealTraits>::Rhs>();},
  }; }

inline auto testCoherence(Options::UnificationWithAbstraction uwa)
{ 
  auto s = state(uwa);
  return LascaSimplRule<Coherence<RealTraits>>(Coherence<RealTraits>(s), Normalization(s));
}



REGISTER_GEN_TESTER(Test::Generation::GenerationTester<LascaSimplRule<Coherence<RealTraits>>>(testCoherence(UWA_MODE)))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(a + b)) )  }) })
      .expected(exactly(
            clause({ p(a + b)  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(2 * a + b)) )  }) })
      .expected(exactly(
            clause({ p(a + b + floor(a))  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(     p(floor(2 * a + b)) )  }) })
      .expected(exactly(
            clause({ p(a + b + floor(a))  })
      ))
    )


TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(     p(floor(2 * a + 2 * b)) )  }) })
      .expected(exactly(
            clause({ p(2 * a + 2 * b)  })
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( 2 * a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(a + b)) )  }) })
      .expected(exactly(
          /* nothing */ 
      ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( f(x) + f(y) == floor(f2(x,y)) )  }) 
                , clause({ selected(     p(floor(f(a) + f(b))) )  }) })
      .expected(exactly(
            clause({ p(f(a) + f(b))  })
      ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(f2(a, x) + f2(y, b)) )  }) 
                , clause({ selected(     p(floor(f2(a, x) + f2(y, b))) )  }) })
      .expected(exactly(
            clause({ p(f2(a, x) + f2(y, b))  })
      ))
    )

TEST_GENERATION(basic08,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(f2(a, x) + 2 * f2(y, b)) )  }) 
                , clause({ selected(     p(floor(2 * f2(a, x) + f2(y, b))) )  }) })
      .expected(exactly(
            clause({ p(3 * f2(a, b))  })
      ))
    )

TEST_GENERATION(basic09,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected(  isInteger(f(x)) )  }) 
                , clause({ selected(     p(floor(f(a) + f(b))) )  }) })
      .expected(exactly(
              clause({ p(f(a) + floor(f(b)))  })
            , clause({ p(f(b) + floor(f(a)))  })
      ))
    )


TEST_GENERATION(basic10,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(p(floor(-a + -b)) )  }) })
      .expected(exactly(
          clause({ p(-a + -b) })
      ))
    )

TEST_GENERATION(basic11,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(3 * f(a)) )  }) 
                , clause({ selected(p(floor(f(x) + f(y) + f(z))) )  }) })
      .expected(exactly(
          clause({ p(3 * f(a)) })
      ))
    )

TEST_GENERATION(basic12,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(f(x) + f(y) + f(z))) }) 
                , clause({ selected(p(floor(3 * f(a)) )) }) })
      .expected(exactly(
          clause({ p(3 * f(a)) })
      ))
    )

TEST_GENERATION(factors_0,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(a + b + c)) )  }) })
      .expected(exactly(
          clause({ p(a + b + c) })
      ))
    )

TEST_GENERATION(factors_1,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + -c)) )  }) })
      .expected(exactly(
          clause({ p(-a + -b + -c) })
      ))
    )

TEST_GENERATION(factors_2,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + b + -c)) )  }) })
      .expected(exactly(
          /* nothing */
      ))
    )

TEST_GENERATION(factors_3,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + 2 * c)) )  }) })
      .expected(exactly(
          /* nothing */
      ))
    )

TEST_GENERATION(factors_4,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + -2 * c)) )  }) })
      .expected(exactly(
          clause({ p(-a + -b + -c + floor(-c)) })
      ))
    )

TEST_GENERATION(factors_5,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(a + b + 2 * c)) )  }) })
      .expected(exactly(
          clause({ p(a + b + c + floor(c)) })
      ))
    )

// TODO check theory whether we really should do this with factors != +-1
TEST_GENERATION(factors_6,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(2 * a + 4 * b + 2 * c)) )  }) })
      .expected(exactly(
          clause({ p(2 * a + 2 * b + 2 * c + floor(2 * b)) })
      ))
    )

TEST_GENERATION(factors_7,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(frac(1,2) * a + 4 * b + 2 * c)) )  }) })
      .expected(exactly(
          /* nothing */
      ))
    )
//
unsigned factorial(unsigned n) {
  if (n <= 1) {
    return 1;
  } else {
    return n * factorial(n - 1);
  }
}
unsigned choices(unsigned n, unsigned k) {
  ASS(n >= k)
  return factorial(n) / factorial(n - k);
}

// unsigned bellNumber(unsigned n) {
//   if (n == 0) {
//     return 1;
//   } else {
//     return range(0, n)
//       .map([n](auto k) { 
//           return choices(n - 1, k) * bellNumber(k);
//       }).sum();
//   }
// }


unsigned bellNumber(unsigned n) {
  ASS(n != 0)
  RStack<unsigned> triangle;
  triangle->push(1);
  unsigned start0 = 0;
  unsigned len0 = 1;
  while (n != 1) {
    unsigned start1 = triangle->size() - 1;
    for (unsigned i : range(0, len0)) {
      triangle->push(triangle[start0 + i] + triangle[start1 + i]);
    }
    len0 += 1;
    start0 = start1;
    n--;
  }
  return triangle->top();
}

TEST_FUN(bla_bla) {
  auto N = 6;
  PartitionIter iter(N);
  for (auto i : range(1, bellNumber(N))) {
    std::cout << iter << std::endl;
    ASS_REP(iter.nextPartition(), i)
  }
  ASS(!iter.nextPartition())
}
