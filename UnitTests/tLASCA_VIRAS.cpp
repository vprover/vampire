/*
 * This file is part of the source code of the software program Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/LASCA.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/LASCA/VIRAS.hpp"
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
#include "Inferences/LASCA/Normalization.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;
using namespace Inferences::LASCA;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num}, Num)                                                                                    \
  DECL_FUNC(f2, {Num, Num}, Num)                                                                               \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_CONST(d, Num)                                                                                          \
  DECL_CONST(e, Num)                                                                                          \
  DECL_PRED(R, {Num,Num})                                                                                     \
  DECL_PRED(P, {Num})                                                                                         \

#define MY_SYNTAX_SUGAR SUGAR(Rat)

template<class Rule>
struct LascaSimplRule 
  : public SimplifyingGeneratingInference
{
  Rule _rule;
  LASCA::Normalization _norm;
  LascaSimplRule(Rule r, LASCA::Normalization n) : _rule(std::move(r)), _norm(std::move(n)) {}

  void attach(SaturationAlgorithm* salg) final override {
    _rule.attach(salg);
    _norm.attach(salg);
  }

  void detach() final override {
    _rule.detach();
    _norm.detach();
  }

  ClauseGenerationResult generateSimplify(Clause* premise) final override {
    auto res = _rule.generateSimplify(premise);
    return ClauseGenerationResult {
      .clauses = pvi(iterTraits(std::move(res.clauses))
            .filterMap([this](auto cl) { 
              auto simpl = _norm.simplify(cl);
              return someIf(simpl != nullptr, [&]() { return simpl; }); })),
      .premiseRedundant = res.premiseRedundant,
    };
  }

#if VDEBUG
  virtual void setTestIndices(Stack<Indexing::Index*> const& i) final override {
    _rule.setTestIndices(i);
    _norm.setTestIndices(i);
  }
#endif



};

auto testVirasQuantifierElimination(
    Options::UnificationWithAbstraction uwa = Options::UnificationWithAbstraction::LPAR_MAIN
    )
{ 
  auto state = testLascaState(uwa);
  return LascaSimplRule<VirasQuantifierElimination>(VirasQuantifierElimination(state), Normalization(state));
}

template<class Rule>
struct LascaGenerationTester : public Test::Generation::GenerationTester<LascaSimplRule<Rule>> 
{
  LascaGenerationTester(LascaSimplRule<Rule> rule) 
    : Test::Generation::GenerationTester<LascaSimplRule<Rule>>(std::move(rule)) {}


  virtual bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs)
  { 
    auto state = testLascaState();
    return TestUtils::permEq(*lhs, *rhs, [&](auto l, auto r) { return state->equivalent(l,r); });
  }

};



REGISTER_GEN_TESTER(LascaGenerationTester<VirasQuantifierElimination>(testVirasQuantifierElimination()))
// REGISTER_GEN_TESTER(Test::Generation::GenerationTester<LascaSimplRule<VirasQuantifierElimination>>(testVirasQuantifierElimination()))

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(ported_lra_test_basic01,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, x + b > 0 }) })
      .expected(exactly(
            clause({})
      ))
      .premiseRedundant(true)
    )
TEST_GENERATION(ported_lra_test_basic02,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0 }) })
      .expected(exactly(
            clause({ a + b > 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_basic03,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0, f(y) + c > 0 }) })
      .expected(exactly(
        clause({a + b > 0, f(y) + c > 0 }) 
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_basic04,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c >= 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_basic05,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, - x - c >= 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 })
      ))
      .premiseRedundant(true)
    )


/////////////////////////////////////////////////////////
// Only use unshielded variables
//////////////////////////////////////

TEST_GENERATION(ported_lra_test_shielded01,
    Generation::SymmetricTest()
      .inputs ({  clause({x + a > 0, - x + b > 0, f(x) + c > 0 }) })
      .expected(exactly())
      .premiseRedundant(false)
    )

TEST_GENERATION(ported_lra_test_shielded02,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, - x + b > 0, P(x) }) })
      .expected(exactly())
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// EQ TEST
//////////////////////////////////////

TEST_GENERATION(ported_lra_test_eq01a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a >= 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq01b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a >= 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq02a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq02b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ a + b >= 0, P(y) }),
            clause({ P(y) }) // TODO can we detect redundancies of that kind?
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_eq03a,
    Generation::SymmetricTest()
      .inputs ({  clause({ -x + a > 0, x - b == 0, P(y) }) })
      .expected(exactly(
            clause({ P(y) }), // TODO can we detect redundancies of that kind?
            clause({ a - b >= 0, P(y) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq03b,
    Generation::SymmetricTest()
      .inputs ({  clause({ -x + a > 0, - x + b == 0, P(y) }) })
      .expected(exactly(
            clause({ P(y) }), // TODO can we detect redundancies of that kind?
            clause({ a - b >= 0, P(y) })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq04a,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, - x - c == 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 }),
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_eq04b,
    Generation::SymmetricTest()
      .inputs ({  clause({ x + a > 0, -x + b >= 0, x + c == 0 }) })
      .expected(exactly(
            clause({ a + b >= 0, a - c >= 0 }),
            clause({ a + b >= 0, b + c >= 0 })
      ))
      .premiseRedundant(true)
    )

/////////////////////////////////////////////////////////
// NOT EQ TEST
//////////////////////////////////////


TEST_GENERATION(ported_lra_test_neq1a,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != x + a , 0 != x + b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_neq1b,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -x - a , 0 != x + b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_neq1c,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -x - a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )


TEST_GENERATION(ported_lra_test_neq1d,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != x + a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != a - b })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_neq2,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != 2 * x + a , 0 != -x - b })})
      .expected(exactly(
            clause({ 0 != frac(1,2) * a - b })
      ))
      .premiseRedundant(true)
    )

  // TODO


TEST_GENERATION(ported_lra_test_misc01,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -3 * x +               f2(y,z) , 0 != x + -10 * z })})
                       // 0 !=      x +        -(1/3) f2(y,z) , 0 != x + -10 * z
      .expected(exactly(anyOf(
            clause({ 0 !=  10 * z + frac(-1, 3) * f2(y,z) }), 
            clause({ 0 != -10 * z + frac( 1, 3) * f2(y,z) })
      )))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_misc02,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != 30 * x +          f2(y,z) , 0 != 2 * x +       y })})
      .expected(exactly(
                 clause({ 0 != -15 * y +  f2(y,z)  }), // TODO optimization for this case
                 clause({ 0 !=  15 * y + -f2(y,z)  })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_bug02a,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 == y + -1 , 0 != y + -c })})
      .expected(exactly(
            clause({ -c + 1 == 0             })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_bug03,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != -1 + -x + -3 * f(x) + y 
                             , 0 !=  1 +  x +  3 * f(x) - y })})
      .expected(exactly(
            clause({  }),
            clause({  })
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(ported_lra_test_bug04,
    Generation::SymmetricTest()
      // .inputs ({         clause({ y - x >= 0, x - z >= 0, f(z) - f(y) > 0})})
      .inputs ({         clause({ -x + y >= 0, x + -z >= 0, -f(y) + f(z) > 0 })})
      .expected(exactly( clause({ y             - z >= 0, f(z) - f(y) > 0}) ))
      .premiseRedundant(true)
    )

// TEST_GENERATION(ported_lra_test_bug05,
//     Generation::SymmetricTest()
//     .inputs({clause({
//           -5 * x + e + -4 * f(z) + -7 * b >= 0,
//           -4 * x +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0,
//           15 + 15 * x + 6 * y + -17 * b >= 0,
//         })
//       })
//     // elimSet 
//     //  1/5 * e + -4/5 * f(z) - 7/5 * b + ε
//     //  -19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε
//     //  -∞
//       .expected(exactly( 
//           // clause[x//-∞] = true
//           // clause[x//1/5 * e + -4/5 * f(z) - 7/5 * b + ε] 
//           // = -4 * x +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0 \/ 15 + 15 * x + 6 * y + -17 * b >= 0 [x // 1/5 * e + -4/5 * f(z) - 7/5 * b + ε]
//           // = -4 * (1/5 * e + -4/5 * f(z) - 7/5 * b + ε) +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0 \/ 15 + 15 * (1/5 * e + -4/5 * f(z) - 7/5 * b + ε) + 6 * y + -17 * b >= 0
//           // = -4/5 * e + 16/5 * f(z) + 28/5 * b - ε +  -19 * g(z) + - c * y  + - (d * f(z)) >= 0 \/ 15 + 3 * e + -12/5 * f(z) - 21/5 * b + ε + 6 * y + -17 * b >= 0
//           // = -4/5 * e + 16/5 * f(z) + 28/5 * b +  -19 * g(z) + - c * y  + - (d * f(z)) - ε >= 0 \/ 15 + 3 * e + -12/5 * f(z) - 21/5 * b + 6 * y + -17 * b + ε >= 0
//           // = -4/5 * e + 16/5 * f(z) + 28/5 * b +  -19 * g(z) + - c * y  + - (d * f(z))     >  0 \/ 15 + 3 * e + -12/5 * f(z) - 21/5 * b + 6 * y + -17 * b     >= 0
//           clause({ -frac(4,5) * e + frac(16,5) * f(z) + frac(28,5) * b +  -19 * g(z) + - c * y  + - (d * f(z)) > 0,  15 + 3 * e + -frac(12,5) * f(z) - frac(21,5) * b + 6 * y + -17 * b >= 0 })
//           // clause[ x // -19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε ] = 
//           // = -5 * x + e + -4 * f(z) + -7 * b >= 0 \/  15 + 15 * x + 6 * y + -17 * b >= 0 [ x // -19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε ]
//           // = -5 * (-19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε) + e + -4 * f(z) + -7 * b >= 0 \/  15 + 15 * (-19/4 * g(z) - 1/4 * c * y - 1/4 * d * f(z) + ε) + 6 * y + -17 * b >= 0
//           // = 95/4 * g(z) + 5/4 * c * y + 5/4 * d * f(z) - ε + e + -4 * f(z) + -7 * b >= 0 \/  15 + -285/4 * g(z) - 15/4 * c * y - 15/4 * d * f(z) + ε + 6 * y + -17 * b >= 0
//           // = 95/4 * g(z) + 5/4 * c * y + 5/4 * d * f(z) + e + -4 * f(z) + -7 * b - ε >= 0 \/  15 + -285/4 * g(z) - 15/4 * c * y - 15/4 * d * f(z) + 6 * y + -17 * b + ε >= 0
//           // = 95/4 * g(z) + 5/4 * c * y + 5/4 * d * f(z) + e + -4 * f(z) + -7 * b     >  0 \/  15 + -285/4 * g(z) - 15/4 * c * y - 15/4 * d * f(z) + 6 * y + -17 * b     >= 0
//           ,clause({frac(95,4) * g(z) + frac(5,4) * c * y + frac(5,4) * d * f(z) + e + -4 * f(z) + -7 * b     >  0,  15 + -frac(285,4) * g(z) - frac(15,4) * c * y - frac(15,4) * d * f(z) + 6 * y + -17 * b     >= 0})
//           // clause({
//           //  1 + frac(6,15) * y + frac(-17,15) * b + frac(1,5) * e + frac(-4,5) * f(z) + frac(-7,5) * b >= 0,
//           //  1 + frac(6,15) * y + frac(-17,15) * b + frac(-19,4) * g(z) + frac(-1,4) * c * y  + frac(-1,4) * (d * f(z)) >= 0,
//           //     }) 
//           ))
//       .premiseRedundant(true)
//     )



TEST_GENERATION(to_optimize_2,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != a - x, 0 != b - x })})
      .expected(exactly(
                   clause({ 0 != b - a  })
                 , clause({ 0 != a - b  }) 
        // TODO optimization for this case to only one of the two results
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(to_optimize_3,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != a - x, 0 != b - x, 0 != c - x })})
      .expected(exactly(
                   clause({             0 != b - a, 0 != c - a  })
                 , clause({ 0 != a - b            , 0 != c - b  }) 
                 , clause({ 0 != a - c, 0 != b - c              })
        // TODO optimization for this case to only one of the three results
      ))
      .premiseRedundant(true)
    )

TEST_GENERATION(to_optimize_4,
    Generation::SymmetricTest()
      .inputs ({  clause({ 0 != a - x, 0 != b - x, 0 != c - x, 0 != d - x })})
      .expected(exactly(
                   clause({             0 != b - a, 0 != c - a, 0 != d - a  })
                 , clause({ 0 != a - b            , 0 != c - b, 0 != d - b  })
                 , clause({ 0 != a - c, 0 != b - c            , 0 != d - c  })
                 , clause({ 0 != a - d, 0 != b - d, 0 != c - d              })
        // TODO optimization for this case to only one of the four results
      ))
      .premiseRedundant(true)
    )


  // TODO test -x + bla == 0 vs -x + -bla == 0
