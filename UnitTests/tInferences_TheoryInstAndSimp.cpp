/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#if VZ3

#include "Test/SyntaxSugar.hpp"
#include "Inferences/TheoryInstAndSimp.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/GenerationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;

namespace {

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST UNIT INITIALIZATION
/////////////////////////////////////
#define DECL_VARS                                                                                             \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_VAR(x0, 0)                                                                                             \
  DECL_VAR(x1, 1)                                                                                             \
  DECL_VAR(x2, 2)                                                                                             \
  DECL_VAR(x3, 3)                                                                                             \
  DECL_VAR(x4, 4)                                                                                             \

#define DECL_LIST(sort)                                                                                       \
  DECL_SORT(list)                                                                                             \
                                                                                                              \
  DECL_CONST(nil, list)                                                                                       \
  DECL_FUNC(cons, { sort, list  }, list)                                                                      \
                                                                                                              \
  DECL_TERM_ALGEBRA(list, {nil, cons})                                                                        \
  __ALLOW_UNUSED(                                                                                             \
    auto head = cons.dtor(0);                                                                                 \
    auto tail = cons.dtor(1);                                                                                 \
  )                                                                                                           \

#define LIST_INT_SUGAR                                                                                        \
  NUMBER_SUGAR(Int)                                                                                           \
  DECL_VARS                                                                                                   \
                                                                                                              \
  DECL_FUNC(f, {Int}, Int)                                                                                    \
  DECL_PRED(p, {Int})                                                                                         \
  DECL_PRED(q, {Int})                                                                                         \
  DECL_PRED(r, {Int,Int})                                                                                     \
                                                                                                              \
                                                                                                              \
  DECL_LIST(Int)                                                                                              \
                                                                                                              \
  DECL_PRED(pL, {list})                                                                                       \

#define NAT_SUGAR                                                                                             \
  DECL_SORT(nat)                                                                                              \
  DECL_CONST(zero, nat)                                                                                       \
  DECL_FUNC(s, {nat}, nat)                                                                                    \
  DECL_TERM_ALGEBRA(nat, {zero, s})                                                                           \
  __ALLOW_UNUSED(                                                                                             \
    auto p = s.dtor(0);                                                                                       \
  )                                                                                                           \
                                                                                                              \
  DECL_PRED(q, {nat})                                                                                         \
  DECL_VARS                                                                                                   \


#define MY_GEN_RULE     TheoryInstAndSimp
#define MY_GEN_TESTER   Generation::GenerationTester
#define MY_SYNTAX_SUGAR LIST_INT_SUGAR

///////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES
/////////////////////////////////////

OptionMap options(const char* mode, bool withGeneralization = false) {
  return {
    { "theory_instantiation", mode },
    { "theory_instantiation_tautology_deletion", "on" },
    { "theory_instantiation_generalisation", withGeneralization ? "on" : "off" },
  };
}

TEST_GENERATION(test_01,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({ x == 1, x * y != 6, ~(0 < x), ~(x < y), r(x,y)  })   })
      .expected(exactly(
            clause({ r(2,3)  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(test_02,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({  tail(x) != tail(y), 
          head(x) != 0, 
          head(y) != 1, 
          tail(x) != nil(), 
          p(head(tail(x))), p(head(tail(y)))  })   })
      .expected(exactly(
            clause({  p(head(tail(cons(0, nil())))), p(head(tail(cons(1,nil()))))  })
      ))
      .premiseRedundant(false)
    )

#define LIST_ALPHA_SUGAR                                                                                      \
  DECL_VARS                                                                                                   \
  DECL_SORT(alpha)                                                                                            \
  DECL_LIST(alpha)                                                                                            \
  DECL_CONST(a, alpha)                                                                                        \
  DECL_PRED(p, {list})                                                                                        \

TEST_GENERATION_WITH_SUGAR(test_03,
    MY_GEN_RULE, MY_GEN_TESTER, LIST_ALPHA_SUGAR, 
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({  cons(a, nil()) != cons(x, nil()), 
          p(x)  })   })
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

#define RAT_SYNTAX_SUGAR                                                                                      \
    DECL_VARS                                                                                                 \
    NUMBER_SUGAR(Rat)                                                                                         \
    DECL_PRED(p, {Rat,Rat})                                                                                   \

#define TEST_GENERATION_RAT(name, ...) \
  TEST_GENERATION_WITH_SUGAR(name, MY_GEN_RULE, MY_GEN_TESTER, RAT_SYNTAX_SUGAR, __VA_ARGS__)

TEST_GENERATION_RAT(test_04,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({ x != 1, y != 4, p(x,y) })    })
      .expected(exactly())
      .premiseRedundant(false)
    )

TEST_GENERATION_RAT(test_05,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({ x + y != 0, x != 7, p(x,y) })    })
      .expected(exactly(clause({p(7, -7)})))
      .premiseRedundant(false)
    )


TEST_GENERATION_RAT(test_06,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({ x + y != 0 * z, x != 7, p(x,y) })    })
      .expected(exactly(clause({p(7, -7)})))
      .premiseRedundant(false)
    )

TEST_GENERATION_RAT(test_07,
    Generation::SymmetricTest()
      .options(options("strong"))
      .inputs({    clause({ x + y != 0 * z, x != 7, p(x,y) })    })
      .expected(exactly(clause({p(7, -7)})))
      .premiseRedundant(false)
    )

#define INT_SYNTAX_SUGAR                                                                                      \
    DECL_VARS                                                                                                 \
    NUMBER_SUGAR(Int)                                                                                         \
    DECL_PRED(p, {Int,Int})                                                                                   \

#define TEST_GENERATION_INT(name, ...) \
  TEST_GENERATION_WITH_SUGAR(name, MY_GEN_RULE, MY_GEN_TESTER, INT_SYNTAX_SUGAR, __VA_ARGS__)

TEST_GENERATION_INT(test_08,
    Generation::SymmetricTest()
      .options(options("overlap"))
      .inputs({    clause({ ~(0 <= x), ~(x <= 1), x == 1, p(x,x) })    })
      .expected(exactly(clause({p(0, 0)})))
      .premiseRedundant(false)
    )

TEST_GENERATION_INT(test_09,
    Generation::SymmetricTest()
      .options(options("overlap"))
      .inputs({    clause({ ~(0 <= x), ~(x <= 1), x == 0, p(x,x) })    })
      .expected(exactly(clause({p(1, 1)})))
      .premiseRedundant(false)
    )

TEST_GENERATION_INT(test_all_vs_strong_1a,
    Generation::SymmetricTest()
      .options(options("strong"))
      .inputs({    clause({ ~(-1 < x), ~(x < 1), x == 0, p(x,y) })    })
      .expected(exactly(clause({num(0) == 0, p(0, y)})))
      .premiseRedundant(false)
    )

TEST_GENERATION_INT(test_all_vs_strong_1b,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({ ~(-1 < x), ~(x < 1), x == 0, p(x,y) })    })
      .expected(exactly(  ))
      .premiseRedundant(true)
    )

TEST_GENERATION_INT(test_all_vs_strong_2a,
    Generation::SymmetricTest()
      .options(options("strong"))
      .inputs({    clause({ x == 7, x != 7, p(x,y) })    })
      .expected(exactly(clause({ 7 == num(7), p(7, y)})))
      .premiseRedundant(false)
    )

TEST_GENERATION_INT(test_all_vs_strong_2b,
    Generation::SymmetricTest()
      .options(options("all"))
      .inputs({    clause({ x == 7, x != 7, p(x,y) })    })
      .expected(exactly(  ))
      .premiseRedundant(true)
    )

TEST_GENERATION_INT(test_overlap_vs_strong_1a,
    Generation::SymmetricTest()
      .options(options("overlap"))
      .inputs({    clause({ ~(0 <= x), ~(x <= 0), x == 0, p(x,x) })    })
      .expected(exactly())
      .premiseRedundant(true)
    )

TEST_GENERATION_INT(test_overlap_vs_strong_1b,
    Generation::SymmetricTest()
      .options(options("strong"))
      .inputs({    clause({ ~(0 <= x), ~(x <= 0), x == 0, p(x,x) })    })
      .expected(exactly(clause({ 0 == num(0), p(0, 0)})))
      .premiseRedundant(false)
    )

TEST_GENERATION_INT(test_overlap_vs_strong_2,
    Generation::SymmetricTest()
      .options(options("overlap"))
      .inputs({    clause({ ~(0 <= x), ~(x <= 0), y == 0, p(x,y) })    })
      .expected(exactly(clause({ 0 == y, p(0, y)})))
      .premiseRedundant(false)
    )

#define PAIR_SYNTAX_SUGAR                                                                                     \
  DECL_VARS                                                                                                   \
  NUMBER_SUGAR(Int)                                                                                           \
  DECL_SORT(Pair)                                                                                             \
                                                                                                              \
  DECL_FUNC(pair, { Int, Int },  Pair)                                                                        \
                                                                                                              \
  DECL_TERM_ALGEBRA(Pair, {pair})                                                                             \
  __ALLOW_UNUSED(                                                                                             \
    auto fst = pair.dtor(0);                                                                                  \
    auto snd = pair.dtor(1);                                                                                  \
  )                                                                                                           \
                                                                                                              \
  DECL_PRED(p, { Int })                                                                                       \

#define TEST_GENERATION_PAIR(name, ...) \
  TEST_GENERATION_WITH_SUGAR(name, MY_GEN_RULE, MY_GEN_TESTER, PAIR_SYNTAX_SUGAR, __VA_ARGS__)

#define TEST_GENERATION_LIST_INT(name, ...) \
  TEST_GENERATION_WITH_SUGAR(name, MY_GEN_RULE, MY_GEN_TESTER, LIST_INT_SUGAR, __VA_ARGS__)

TEST_GENERATION_PAIR(bug_01,
    Generation::SymmetricTest()
      .options          (options("all"))
      .inputs           ({clause({ 0 == fst(pair(0,127)) })   })
      .expected         (exactly(  ))
      .premiseRedundant (true)
    )

TEST_GENERATION_LIST_INT(bug_02,
    Generation::SymmetricTest()
      .options          (options("all"))
      .inputs           ({clause({ tail(nil) == nil  })   })
      .expected         (exactly(  ))
      .premiseRedundant (false)
    )

TEST_GENERATION_PAIR(bug_03,
    Generation::SymmetricTest()
      .options          (options("all"))
      .inputs           ({clause({ 0 != fst(pair(0,127)) })   })
      .expected         (exactly( clause({}) ))
    )

TEST_GENERATION_LIST_INT(bug_04,
    Generation::SymmetricTest()
      .options          (options("all", /* withGeneralization= */true))
      .inputs           ({clause({ nil() != tail(nil()) })   })
      .expected         (exactly())
    )


TEST_GENERATION_PAIR(pair_1,
    Generation::SymmetricTest()
      .options          (options("all"))
      .inputs           ({clause({ 0 != fst(x) + snd(x), 10 != fst(x), p(snd(x)) })   })
      .expected         (exactly( clause({ p(snd(pair(10, -10))) }) ))
    )


TEST_GENERATION_PAIR(generalisation_1,
    Generation::SymmetricTest()
      .options          (options("all", /* withGeneralization= */true))
      .inputs           ({clause({ 10 != fst(x), p(snd(x)) })   })
      .expected         (exactly( clause({ p(snd(pair(10, y))) }) ))
    )



TEST_GENERATION_LIST_INT(generalisation_2,
    Generation::SymmetricTest()
      .options          (options("all", /* withGeneralization= */true))
      .inputs           ({clause({ 10 != head(x) + head(tail(x)), pL(x), head(x) != 2 })   })
      .expected         (exactly( clause({ pL(cons(2, cons(8, y))) }) ))
    )



TEST_GENERATION_LIST_INT(generalisation_3,
    Generation::SymmetricTest()
      .options          (options("all", /* withGeneralization= */true))
      .inputs           ({clause({ 10 != head(x) + head(tail(tail(x))), pL(x), head(x) != 2 })   })
      .expected         (exactly( clause({ pL(cons(2, cons(y, cons(8, z)))) }) ))
    )

TEST_GENERATION_LIST_INT(generalisation_4,
    Generation::AsymmetricTest()
      .options          (options("all", /* withGeneralization= */true))
      .input            (clause({ tail(x) == nil, pL(x) }))
      .expected         (exactly( clause({ pL(cons(x1,cons(x2,x3))) }) ))
    )

TEST_GENERATION_WITH_SUGAR(generalisation_5,
    MY_GEN_RULE, MY_GEN_TESTER, NAT_SUGAR,
    Generation::AsymmetricTest()
      .options          (options("all", /* withGeneralization= */true))
      .input            (clause({ p(p(x)) == zero, q(x) }))
      .expected         (exactly( clause({ q(s(s(s(y)))) }) ))
    )

}

#endif // VZ3
