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

// TODO, don't allow non-minimal results
// if set to true we ignore that some rules return the same result multiple times, or instances of the most general result in addition to the most general result. This should be fixed to not pollute the search space with redundant stuff
#define TESTS_ALLOW_NON_MINIMAL_RESULTS 1

#if TESTS_ALLOW_NON_MINIMAL_RESULTS
#  define expectedResults contains
#else
#  define expectedResults exactly
#endif // TESTS_ALLOW_NON_MINIMAL_RESULTS

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(a + b)) )  }) })
      .expected(expectedResults(
            clause({ p(a + b)  })
      ))
    )

TEST_GENERATION(basic02,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(2 * a + b)) )  }) })
      .expected(expectedResults(
            clause({ p(a + b + floor(a))  })
      ))
    )

TEST_GENERATION(basic03,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(     p(floor(2 * a + b)) )  }) })
      .expected(expectedResults(
            clause({ p(a + b + floor(a))  })
      ))
    )


TEST_GENERATION(basic04,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b) )  }) 
                , clause({ selected(     p(floor(2 * a + 2 * b)) )  }) })
      .expected(expectedResults(
            clause({ p(2 * a + 2 * b)  })
      ))
    )

TEST_GENERATION(basic05,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( 2 * a + b == floor(c) )  }) 
                , clause({ selected(     p(floor(a + b)) )  }) })
      .expected(expectedResults(
          /* nothing */ 
      ))
    )

TEST_GENERATION(basic06,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( f(x) + f(y) == floor(f2(x,y)) )  }) 
                , clause({ selected(     p(floor(f(a) + f(b))) )  }) })
      .expected(expectedResults(
            clause({ p(f(a) + f(b))  })
      ))
    )

TEST_GENERATION(basic07,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(f2(a, x) + f2(y, b)) )  }) 
                , clause({ selected(     p(floor(f2(a, x) + f2(y, b))) )  }) })
      .expected(expectedResults(
            clause({ p(f2(a, x) + f2(y, b))  })
      ))
    )

TEST_GENERATION(basic08,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(f2(a, x) + 2 * f2(y, b)) )  }) 
                , clause({ selected(     p(floor(2 * f2(a, x) + f2(y, b))) )  }) })
      .expected(expectedResults(
            clause({ p(3 * f2(a, b))  })
      ))
    )

TEST_GENERATION(basic09,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected(  isInteger(f(x)) )  }) 
                , clause({ selected(     p(floor(f(a) + f(b))) )  }) })
      .expected(expectedResults(
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
      .expected(expectedResults(
          clause({ p(-a + -b) })
      ))
    )

TEST_GENERATION(basic11,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(3 * f(a)) )  }) 
                , clause({ selected(p(floor(f(x) + f(y) + f(z))) )  }) })
      .expected(expectedResults(
          clause({ p(3 * f(a)) })
      ))
    )

TEST_GENERATION(basic12,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(f(x) + f(y) + f(z))) }) 
                , clause({ selected(p(floor(3 * f(a)) )) }) })
      .expected(expectedResults(
          clause({ p(3 * f(a)) })
      ))
    )

TEST_GENERATION(factors_0,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(a + b + c)) )  }) })
      .expected(expectedResults(
          clause({ p(a + b + c) })
      ))
    )

TEST_GENERATION(factors_1,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + -c)) )  }) })
      .expected(expectedResults(
          clause({ p(-a + -b + -c) })
      ))
    )

TEST_GENERATION(factors_2,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + b + -c)) )  }) })
      .expected(expectedResults(
          /* nothing */
      ))
    )

TEST_GENERATION(factors_3,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + 2 * c)) )  }) })
      .expected(expectedResults(
          /* nothing */
      ))
    )

TEST_GENERATION(factors_4,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(-a + -b + -2 * c)) )  }) })
      .expected(expectedResults(
          clause({ p(-a + -b + -c + floor(-c)) })
      ))
    )

TEST_GENERATION(factors_5,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(a + b + 2 * c)) )  }) })
      .expected(expectedResults(
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
      .expected(expectedResults(
          clause({ p(2 * a + 2 * b + 2 * c + floor(2 * b)) })
      ))
    )

TEST_GENERATION(factors_7,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(a + b + c) )  }) 
                , clause({ selected(p(floor(frac(1,2) * a + 4 * b + 2 * c)) )  }) })
      .expected(expectedResults(
          /* nothing */
      ))
    )

TEST_GENERATION(vars_0,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(a + f(b))) )  }) })
      .expected(expectedResults(
          /* nothing */
      ))
    )

TEST_GENERATION(vars_1,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(a + f(a))) )  }) })
      .expected(expectedResults(
                  clause({          p(      a + f(a))     })
      ))
    )

TEST_GENERATION(vars_2,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                , clause({ selected(p(floor(2 * a + f(a))) )  }) })
      .expected(expectedResults(
                  clause({          p(floor(a) + a + f(a))     })
      ))
    )

TEST_GENERATION(vars_3,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(y) + g(x)) )  }) 
                 , clause({ selected(p(floor(a + f(a) + g(b))) )  }) })
      .expected(expectedResults(

      ))
    )

TEST_GENERATION(vars_4,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(y) + g(x)) )  }) 
                 , clause({ selected(p(floor(a + f(b) + g(a))) )  }) })
      .expected(expectedResults(
                  clause({          p(g(a) + a + f(b))     })
      ))
    )

TEST_GENERATION(vars_5,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(b + f(b))) )  }) })
      .expected(expectedResults(
                  clause({          p(b + f(b))     })
      ))
    )

TEST_GENERATION(vars_6,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(y + g(y))) )  }) })
      .expected(expectedResults(
      ))
    )

TEST_GENERATION(vars_7,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(a + b + f(a + b))) )  }) })
      .expected(expectedResults(
                   clause({ p(a + b + f(a + b))  }) 
      ))
    )

TEST_GENERATION(vars_8,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(a + 2 * b + f(a + b))) )  }) })
      .expected(expectedResults(
                   clause({ p(a + b + f(a + b) + floor(b)) }) 
      ))
    )

TEST_GENERATION(vars_9,
    Generation::SymmetricTest()
      .indices(lascaCoherenceIndices())
      .selfApplications(false)
      .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
                 , clause({ selected(p(floor(a + f(y))) )  }) })
      .expected(EXPECTED_TODO())
      // can be p(    a + f(a)                   )
      // can be p(0.9 a + f(0.9 a) + floor(0.1 a))
      // can be p(0.5 a + f(0.5 a) + floor(0.5 a))
      // can be p(0.1 a + f(0.1 a) + floor(0.9 a))
      // can be p(        f(0    ) + floor(  1 a))
    )

// TEST_GENERATION(vars_6,
//     Generation::SymmetricTest()
//       .indices(lascaCoherenceIndices())
//       .selfApplications(false)
//       .inputs  ({ clause({ selected( isInteger(x + f(x)) )  }) 
//                  , clause({ selected(p(floor(b + f(b + y) + a + c)) )  }) })
//       .expected(expectedResults(
//                   clause({          p(b + a + f(b + a) + floor(c))    })
//                 , clause({          p(b + c + f(b + c) + floor(a))    })
//                 , clause({          p(b + f(b) + floor(c + a))    })
//                 , clause({          p(b + a + c + f(b + a + c))    })
//       ))
//     )

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

struct FilterNone {
  friend std::ostream& operator<<(std::ostream& out, FilterNone const& self)
  { return out << "FilterNone"; }
  void undoLastMerge() {}
  bool tryMerge(unsigned p0,unsigned i0, unsigned i1, unsigned p1) { return true; }
};

struct TestFilter {

  friend std::ostream& operator<<(std::ostream& out, TestFilter const& self)
  { return out << self.partitionHistory.size() << self.partitionHistory.top(); }

  Stack<std::pair<unsigned, unsigned>> disallowed;

  Stack<Stack<Stack<unsigned>>> partitionHistory;
  // Stack<Stack<unsigned>> partitions;

  // Stack<unsigned> lastMerge;

  // DHMap<unsigned, unsigned> roots;

  TestFilter(Stack<std::pair<unsigned, unsigned>> disallowed, unsigned N)
    : disallowed(std::move(disallowed))
    , partitionHistory({range(0,unsigned(N)).map([](auto x) { return Stack<unsigned>{x}; }).template collect<Stack>()})
  {

    }
  void undoLastMerge() {
    partitionHistory.pop();
    // roots.remove(lastMerge.pop());
  }

  // unsigned root(unsigned elem) {
  //   while (true) {
  //     auto root = roots.find(elem);
  //     if (root) {
  //       elem = *root;
  //     } else {
  //       return elem;
  //     }
  //   }
  // }

  bool tryMerge(unsigned part0, unsigned elem0, unsigned part1, unsigned elem1) { 
    auto& lastPart = partitionHistory.top();
    auto setOf = [&](auto p) {
      return arrayIter(lastPart)
              .findPosition([&](auto& set) 
                  { return arrayIter(set).find([&](auto& x) { return x == p; }).isSome(); });
    };
    auto i0 = setOf(elem0).unwrap();
    auto i1 = setOf(elem1).unwrap();
    auto newPart = lastPart;
    newPart[i0].loadFromIterator(arrayIter(newPart[i1]));
    newPart.swapRemove(i1);
    partitionHistory.push(std::move(newPart));
    if (auto pair = arrayIter(disallowed)
        .find([&](auto& pair){
          return arrayIter(partitionHistory.top())
            .any([&](auto set){ 
                return arrayIter(set).find([&](auto& x) { return x == pair.first; }).isSome()
                    && arrayIter(set).find([&](auto& x) { return x == pair.second; }).isSome(); 
            });
          })) {
      undoLastMerge();
      return false;
    } else {
      return true;
    }
  }
};

