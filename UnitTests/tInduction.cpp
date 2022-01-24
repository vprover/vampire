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
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"

#include "Indexing/TermIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/RobSubstitution.hpp"

#include "Inferences/Induction.hpp"

using namespace Test;
using namespace Test::Generation;

#define VARS 100

LiteralIndex* comparisonIndex() {
  return new UnitIntegerComparisonLiteralIndex(new LiteralSubstitutionTree());
}

class GenerationTesterInduction
  : public GenerationTester<Induction>
{
public:
  GenerationTesterInduction()
    : GenerationTester<Induction>(), _subst()
  {}

  /**
   * Generated induction clauses are special in that they contain fresh
   * Skolem constants. In order to check these, we use variables instead
   * of the constants we cannot predefine, and require that these variables
   * are mapped bijectively to the new Skolem constants, hence this override.
   */
  bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) override
  {
    // there can be false positive matches which later (in a different literal
    // or clause) can turn out to be the wrong ones and we have to backtrack
    BacktrackData btd;
    _subst.bdRecord(btd);
    if (!TestUtils::permEq(*lhs, *rhs, [this](Literal* l, Literal* r) -> bool {
      if (l->polarity() != r->polarity() || !l->ground()) {
        return false;
      }
      if (!_subst.match(Kernel::TermList(r), 0, Kernel::TermList(l), 1)) {
        if (l->isEquality() && r->isEquality()) {
          return _subst.match(*r->nthArgument(0), 0, *l->nthArgument(1), 1) &&
            _subst.match(*r->nthArgument(1), 0, *l->nthArgument(0), 1);
        }
        return false;
      }
      // we check that so far each variable is mapped to a unique Skolem constant
      DHMap<TermList, unsigned> inverse;
      for (unsigned i = 0; i < VARS; i++) {
        if (!_subst.isUnbound(i, 0)) {
          auto t = _subst.apply(TermList(i,false),0);
          ASS(t.isTerm()) // l is checked for groundness above
          auto f = t.term()->functor();
          if (!env.signature->getFunction(f)->skolem() || t.term()->arity() > 0) {
            return false;
          }
          unsigned v;
          if (inverse.find(t,v)) {
            return false;
          } else {
            inverse.insert(t,i);
          }
        }
      }
      return true;
    })) {
      _subst.bdDone();
      btd.backtrack();
      return false;
    }
    _subst.bdDone();
    return true;
  }

private:
  Kernel::RobSubstitution _subst;
};

#define TEST_GENERATION_INDUCTION(name, ...)                                                                  \
  TEST_FUN(name) {                                                                                            \
    GenerationTesterInduction tester;                                                                         \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR)                                                                           \
    auto test = __VA_ARGS__;                                                                                  \
    test.run(tester);                                                                                         \
  }                                                                                                           \

/**
 * NECESSARY: We need to tell the tester which syntax sugar to import for creating terms & clauses.
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                    \
  DECL_DEFAULT_VARS                                                                        \
  DECL_VAR(x3,3)                                                                           \
  DECL_VAR(x4,4)                                                                           \
  DECL_VAR(x5,5)                                                                           \
  DECL_VAR(x6,6)                                                                           \
  DECL_VAR(x7,7)                                                                           \
  DECL_VAR(x8,8)                                                                           \
  DECL_VAR(x9,9)                                                                           \
  DECL_VAR(x10,10)                                                                         \
  DECL_VAR(x11,11)                                                                         \
  DECL_VAR(x12,12)                                                                         \
  DECL_VAR(x13,13)                                                                         \
  DECL_VAR(x14,14)                                                                         \
  DECL_VAR(x15,15)                                                                         \
  DECL_VAR(x16,16)                                                                         \
  DECL_VAR(x17,17)                                                                         \
  DECL_VAR(x18,18)                                                                         \
  DECL_VAR(x19,19)                                                                         \
  DECL_VAR(x20,20)                                                                         \
  DECL_VAR(x21,21)                                                                         \
  DECL_SORT(s)                                                                             \
  DECL_SORT(u)                                                                             \
  DECL_CONST(sK1, s)                                                                       \
  DECL_CONST(sK2, s)                                                                       \
  DECL_CONST(sK3, s)                                                                       \
  DECL_CONST(sK4, s)                                                                       \
  DECL_CONST(sK5, u)                                                                       \
  DECL_CONST(b, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  __ALLOW_UNUSED(                                                                          \
    auto r0 = r.dtor(0);                                                                   \
  )                                                                                        \
  DECL_CONST(b1, u)                                                                        \
  DECL_CONST(b2, u)                                                                        \
  DECL_FUNC(r1, {s, u, u}, u)                                                              \
  DECL_FUNC(r2, {u, s}, u)                                                                 \
  DECL_TERM_ALGEBRA(u, {b1, b2, r1, r2})                                                   \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_PRED(p, {s})                                                                        \
  DECL_PRED(q, {u})                                                                        \
  NUMBER_SUGAR(Int)                                                                        \
  DECL_PRED(pi, {Int})                                                                     \
  DECL_FUNC(fi, {Int, s}, Int)                                                             \
  DECL_CONST(sK6, Int)                                                                     \
  DECL_CONST(sK7, Int)                                                                     \
  DECL_CONST(sK8, Int)                                                                     \
  DECL_CONST(bi, Int)

// positive literals are not considered 1
TEST_GENERATION_INDUCTION(test_01,
    Generation::TestCase()
      .options({ { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  p(f(sK1,sK2)) }))
      .expected(none())
    )

// positive literals are not considered 2
TEST_GENERATION_INDUCTION(test_02,
    Generation::TestCase()
      .options({ { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  f(sK1,sK2) == g(sK1) }))
      .expected(none())
    )

// non-ground literals are not considered
TEST_GENERATION_INDUCTION(test_03,
    Generation::TestCase()
      .options({ { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  f(sK1,x) != g(sK1) }))
      .expected(none())
    )

// normal case sik=one
TEST_GENERATION_INDUCTION(test_04,
    Generation::TestCase()
      .options({ { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  ~p(f(sK1,sK2)) }))
      .expected({
        clause({ ~p(f(b,sK2)), p(f(x,sK2)) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(x),sK2)) }),
        clause({ ~p(f(sK1,b)), p(f(sK1,y)) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(y))) }),
      })
    )

// normal case sik=two
TEST_GENERATION_INDUCTION(test_05,
    Generation::TestCase()
      .options({ { "induction", "struct" }, { "structural_induction_kind", "two" } })
      .indices({ comparisonIndex() })
      .input( clause({  ~p(f(sK1,sK2)) }))
      .expected({
        clause({ x != r(r0(x)), p(f(r0(x),sK2)) }),
        clause({ ~p(f(x,sK2)) }),
        clause({ y != r(r0(y)), p(f(sK1,r0(y))) }),
        clause({ ~p(f(sK1,y)) }),
      })
    )

// TODO this case is a bit hard to test since new predicates are introduced,
// so we need to customize the test suite for this even more, checking certain
// properties of these new predicates and matching it with some literals.
// This induction mode is not that useful compared to other sik modes to make
// the effort worthwhile.
// // normal case sik=three
// TEST_GENERATION_INDUCTION(test_06,
//     Generation::TestCase()
//       .options({ { "induction", "struct" }, { "structural_induction_kind", "three" } })
//       .indices({ comparisonIndex() })
//       .input( clause({  f(sK1,sK2) != g(sK1) }))
//       .expected({ })
//     )

// generalizations
TEST_GENERATION_INDUCTION(test_07,
    Generation::TestCase()
      .options({ { "induction_gen", "on" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))) }) )
      .expected({
        // sK1 100
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(x),f(sK2,sK4)),sK1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(r(x)),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))) }),

        // sK1 010
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),y) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),r(y)) != g(f(sK1,f(sK2,sK3))) }),

        // sK1 001
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) == g(f(z,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(r(z),f(sK2,sK3))) }),

        // sK1 110
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(x3),f(sK2,sK4)),x3) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(r(x3)),f(sK2,sK4)),r(x3)) != g(f(sK1,f(sK2,sK3))) }),

        // sK1 101
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(x4),f(sK2,sK4)),sK1) == g(f(x4,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(r(x4)),f(sK2,sK4)),sK1) != g(f(r(x4),f(sK2,sK3))) }),

        // sK1 011
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),x5) == g(f(x5,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),r(x5)) != g(f(r(x5),f(sK2,sK3))) }),

        // sK1 111
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(x6),f(sK2,sK4)),x6) == g(f(x6,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(r(x6)),f(sK2,sK4)),r(x6)) != g(f(r(x6),f(sK2,sK3))) }),

        // sK2 10
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(x7,sK4)),sK1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(r(x7),sK4)),sK1) != g(f(sK1,f(sK2,sK3))) }),

        // sK2 01
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) == g(f(sK1,f(x8,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(r(x8),sK3))) }),

        // sK2 11
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(x9,sK4)),sK1) == g(f(sK1,f(x9,sK3))) }),
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(r(x9),sK4)),sK1) != g(f(sK1,f(r(x9),sK3))) }),

        // sK3 1
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,b))), f(f(g(sK1),f(sK2,sK4)),sK1) == g(f(sK1,f(sK2,x10))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,b))), f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,r(x10)))) }),

        // sK4 1
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,x11)),sK1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,r(x11))),sK1) != g(f(sK1,f(sK2,sK3))) }),
      })
    )

// complex terms
TEST_GENERATION_INDUCTION(test_08,
    Generation::TestCase()
      .options({ { "induction_on_complex_terms", "on" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,g(sK1)))) }) )
      .expected({
        // sK1
        clause({ f(f(g(b),f(sK2,sK3)),b) != g(f(b,f(sK2,g(b)))), f(f(g(x),f(sK2,sK3)),x) == g(f(x,f(sK2,g(x)))) }),
        clause({ f(f(g(b),f(sK2,sK3)),b) != g(f(b,f(sK2,g(b)))), f(f(g(r(x)),f(sK2,sK3)),r(x)) != g(f(r(x),f(sK2,g(r(x))))) }),

        // sK2
        clause({ f(f(g(sK1),f(b,sK3)),sK1) != g(f(sK1,f(b,g(sK1)))), f(f(g(sK1),f(y,sK3)),sK1) == g(f(sK1,f(y,g(sK1)))) }),
        clause({ f(f(g(sK1),f(b,sK3)),sK1) != g(f(sK1,f(b,g(sK1)))), f(f(g(sK1),f(r(y),sK3)),sK1) != g(f(sK1,f(r(y),g(sK1)))) }),

        // sK3
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),f(sK2,x3)),sK1) == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),f(sK2,r(x3))),sK1) != g(f(sK1,f(sK2,g(sK1)))) }),

        // g(sK1)
        clause({ f(f(b,f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,b))), f(f(x4,f(sK2,sK3)),sK1) == g(f(sK1,f(sK2,x4))) }),
        clause({ f(f(b,f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,b))), f(f(r(x4),f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,r(x4)))) }),

        // f(sK2,sK3)
        clause({ f(f(g(sK1),b),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),x5),sK1) == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ f(f(g(sK1),b),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),r(x5)),sK1) != g(f(sK1,f(sK2,g(sK1)))) }),

        // f(g(sK1),f(sK2,sK3))
        clause({ f(b,sK1) != g(f(sK1,f(sK2,g(sK1)))), f(x6,sK1) == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ f(b,sK1) != g(f(sK1,f(sK2,g(sK1)))), f(r(x6),sK1) != g(f(sK1,f(sK2,g(sK1)))) }),

        // f(f(g(sK1),f(sK2,sK3)),sK1)
        clause({ b != g(f(sK1,f(sK2,g(sK1)))), x7 == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ b != g(f(sK1,f(sK2,g(sK1)))), r(x7) != g(f(sK1,f(sK2,g(sK1)))) }),

        // f(sK2,g(sK1))
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,b)), f(f(g(sK1),f(sK2,sK3)),sK1) == g(f(sK1,x8)) }),
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,b)), f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,r(x8))) }),

        // f(sK1,f(sK2,g(sK1)))
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(b), f(f(g(sK1),f(sK2,sK3)),sK1) == g(x9) }),
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(b), f(f(g(sK1),f(sK2,sK3)),sK1) != g(r(x9)) }),

        // g(f(sK1,f(sK2,g(sK1))))
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != b, f(f(g(sK1),f(sK2,sK3)),sK1) == x10 }),
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != b, f(f(g(sK1),f(sK2,sK3)),sK1) != r(x10) }),
      })
    )

// positive literals are considered 1
TEST_GENERATION_INDUCTION(test_09,
    Generation::TestCase()
      .options({ { "induction_neg_only", "off" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  p(sK1) }))
      .expected({
        clause({ p(b), ~p(x), }),
        clause({ p(b), p(r(x)), }),
      })
    )

// positive literals are considered 2
TEST_GENERATION_INDUCTION(test_10,
    Generation::TestCase()
      .options({ { "induction_neg_only", "off" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  sK1 == g(sK1) }))
      .expected({
        clause({ b == g(b), x != g(x), }),
        clause({ b == g(b), r(x) == g(r(x)), }),
      })
    )

// non-unit clauses are considered
TEST_GENERATION_INDUCTION(test_11,
    Generation::TestCase()
      .options({ { "induction_unit_only", "off" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  sK1 != g(sK1), p(g(sK2)), ~p(f(sK1,sK2)) }))
      .expected({
        // 1. literal sK1
        clause({ b != g(b), x == g(x), p(g(sK2)), ~p(f(sK1,sK2)) }),
        clause({ b != g(b), r(x) != g(r(x)), p(g(sK2)), ~p(f(sK1,sK2)) }),

        // 3. literal sK1
        clause({ ~p(f(b,sK2)), p(f(y,sK2)), p(g(sK2)), sK1 != g(sK1) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(y),sK2)), p(g(sK2)), sK1 != g(sK1) }),

        // 3. literal sK2
        clause({ ~p(f(sK1,b)), p(f(sK1,x3)), p(g(sK2)), sK1 != g(sK1) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(x3))), p(g(sK2)), sK1 != g(sK1) }),
      })
    )

// "same induction" (i.e. generalized literal is same) is not done twice
//
// TODO: this should be done with two inputs rather than with a non-unit clause
TEST_GENERATION_INDUCTION(test_12,
    Generation::TestCase()
      .options({ { "induction_unit_only", "off" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  sK1 != g(sK1), sK2 != g(sK2) }))
      .expected({
        clause({ b != g(b), x == g(x), sK2 != g(sK2) }),
        clause({ b != g(b), r(x) != g(r(x)), sK2 != g(sK2) }),
      })
    )

TEST_GENERATION_INDUCTION(test_13,
    Generation::TestCase()
      .options({ { "induction", "int" } })
      .context({ clause({ ~(sK6 < num(1)) }) })
      .indices({ comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        clause({ ~pi(1), ~(x < num(1)) }),
        clause({ ~pi(1), pi(x) }),
        clause({ ~pi(1), ~pi(x+1) }),
      })
    )

// use bounds for upward+downward infinite interval integer induction
TEST_GENERATION_INDUCTION(test_14,
    Generation::TestCase()
      .options({ { "induction", "int" }, { "int_induction_interval", "infinite" } })
      .context({ clause({ ~(sK6 < num(1)) }), clause({ ~(bi < sK6) }) })
      .indices({ comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        // upward induction
        clause({ ~pi(1), ~(x < num(1)) }),
        clause({ ~pi(1), pi(x) }),
        clause({ ~pi(1), ~pi(x+1) }),

        // downard induction
        clause({ ~pi(bi), ~(bi < y) }),
        clause({ ~pi(bi), pi(y) }),
        clause({ ~pi(bi), ~pi(y+num(-1)) }),
      })
    )

// use bounds for upward+downward finite interval integer induction
TEST_GENERATION_INDUCTION(test_15,
    Generation::TestCase()
      .options({ { "induction", "int" }, { "int_induction_interval", "finite" } })
      .context({ clause({ ~(sK6 < num(1)) }), clause({ ~(bi < sK6) }) })
      .indices({ comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        // upward induction
        clause({ ~pi(1), ~(x < num(1)) }),
        clause({ ~pi(1), x < bi }),
        clause({ ~pi(1), pi(x) }),
        clause({ ~pi(1), ~pi(x+1) }),

        // downard induction
        clause({ ~pi(bi), num(1) < y }),
        clause({ ~pi(bi), ~(bi < y) }),
        clause({ ~pi(bi), pi(y) }),
        clause({ ~pi(bi), ~pi(y+num(-1)) }),
      })
    )

// use default bound for downward integer induction,
// but for upward use the bound from index
TEST_GENERATION_INDUCTION(test_16,
    Generation::TestCase()
      .options({ { "induction", "int" },
                 { "int_induction_interval", "infinite" },
                 { "int_induction_default_bound", "on" } })
      .context({ clause({ ~(sK6 < num(0)) }) })
      .indices({ comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        // upward induction
        clause({ ~pi(0), ~(x < num(0)) }),
        clause({ ~pi(0), pi(x) }),
        clause({ ~pi(0), ~pi(x+1) }),

        // downward induction: resulting clauses contain "0 < sK6",
        // since there is no bound to resolve it against
        clause({ ~pi(0), ~(num(0) < y), 0 < sK6 }),
        clause({ ~pi(0), pi(y), 0 < sK6 }),
        clause({ ~pi(0), ~pi(y+num(-1)), 0 < sK6 }),
      })
    )
