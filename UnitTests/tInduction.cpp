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

#define SKOLEM_VAR_MIN 100
#define DECL_SKOLEM_VAR(x, i) DECL_VAR(x, i+SKOLEM_VAR_MIN)

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
  bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs, BacktrackData& btd) override
  {
    // there can be false positive matches which later (in a different literal
    // or clause) can turn out to be the wrong ones and we have to backtrack
    // TODO: are all of these backtracking calls necessary?
    _subst.bdRecord(btd);
    if (!TestUtils::permEq(*lhs, *rhs, [this](Literal* l, Literal* r, BacktrackData& btd) -> bool {
      if (l->polarity() != r->polarity()) {
        return false;
      }
      VList::Iterator vit(r->freeVariables());
      while (vit.hasNext()) {
        auto v = vit.next();
        if (!_varsMatched.count(v)) {
          btd.addBacktrackObject(new MatchedVarBacktrackObject(_varsMatched, v));
          _varsMatched.insert(v);
        }
      }
      _subst.bdRecord(btd);
      if (_subst.match(Kernel::TermList(r), 0, Kernel::TermList(l), 1)) {
        if (matchAftercheck()) {
          _subst.bdDone();
          return true;
        }
      }

      _subst.bdDone();
      btd.backtrack();
      _subst.bdRecord(btd);
      if (l->isEquality() && r->isEquality() &&
        _subst.match(*r->nthArgument(0), 0, *l->nthArgument(1), 1) &&
        _subst.match(*r->nthArgument(1), 0, *l->nthArgument(0), 1))
      {
        if (matchAftercheck()) {
          _subst.bdDone();
          return true;
        }
      }
      _subst.bdDone();
      btd.backtrack();
      return false;
    })) {
      _subst.bdDone();
      btd.backtrack();
      return false;
    }
    _subst.bdDone();
    return true;
  }

private:
  bool matchAftercheck() {
    DHMap<TermList, unsigned> inverse;
    for (const auto& i : _varsMatched) {
      auto t = _subst.apply(TermList(i,false),0);
      unsigned v;
      // we check that each variable encountered so far from
      // the expected set is bijectively mapped to something
      if (inverse.find(t,v)) {
        return false;
      } else {
        inverse.insert(t,i);
      }
      // "Skolem" variables should bind to Skolem constants
      if (i >= SKOLEM_VAR_MIN) {
        if (t.isVar() || !env.signature->getFunction(t.term()->functor())->skolem()) {
          return false;
        }
      // normal variables should bind to variables
      } else {
        if (t.isTerm()) {
          return false;
        }
      }
    }
    return true;
  }

  Kernel::RobSubstitution _subst;
  unordered_set<unsigned> _varsMatched;

  class MatchedVarBacktrackObject : public BacktrackObject {
  public:
    MatchedVarBacktrackObject(unordered_set<unsigned>& s, unsigned i) : _s(s), _i(i) {}
    void backtrack() override {
      _s.erase(_i);
    }
  private:
    unordered_set<unsigned>& _s;
    unsigned _i;
  };
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
  DECL_SKOLEM_VAR(skx0,0)                                                                  \
  DECL_SKOLEM_VAR(skx1,1)                                                                  \
  DECL_SKOLEM_VAR(skx2,2)                                                                  \
  DECL_SKOLEM_VAR(skx3,3)                                                                  \
  DECL_SKOLEM_VAR(skx4,4)                                                                  \
  DECL_SKOLEM_VAR(skx5,5)                                                                  \
  DECL_SKOLEM_VAR(skx6,6)                                                                  \
  DECL_SKOLEM_VAR(skx7,7)                                                                  \
  DECL_SKOLEM_VAR(skx8,8)                                                                  \
  DECL_SKOLEM_VAR(skx9,9)                                                                  \
  DECL_SKOLEM_VAR(skx10,10)                                                                \
  DECL_SKOLEM_VAR(skx11,11)                                                                \
  DECL_SKOLEM_VAR(skx12,12)                                                                \
  DECL_SKOLEM_VAR(skx13,13)                                                                \
  DECL_SKOLEM_VAR(skx14,14)                                                                \
  DECL_VAR(x3,3)                                                                           \
  DECL_VAR(x4,4)                                                                           \
  DECL_VAR(x5,5)                                                                           \
  DECL_SORT(s)                                                                             \
  DECL_SORT(u)                                                                             \
  DECL_SKOLEM_CONST(sK1, s)                                                                \
  DECL_SKOLEM_CONST(sK2, s)                                                                \
  DECL_SKOLEM_CONST(sK3, s)                                                                \
  DECL_SKOLEM_CONST(sK4, s)                                                                \
  DECL_SKOLEM_CONST(sK5, u)                                                                \
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

TEST_FUN(test_tester) {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  GenerationTesterInduction tester;
  BacktrackData btd;
  // first literal is matched both ways but none of them works
  ASS(!tester.eq(
    clause({ r(sK1) == r(x), f(r(sK1),y) != z }),
    clause({ r(skx1) == r(x3), f(r(x3),x4) != x5 }),
    btd));
  // second clause cannot be matched because of x4
  ASS(!tester.eq(
    clause({ r(sK1) == r(x), f(r(sK1),y) != z }),
    clause({ r(skx1) == r(x3), f(r(skx1),x4) != x4 }),
    btd));
  // y is matched to both y4 and y5
  ASS(!tester.eq(
    clause({ r(sK1) == r(x), f(r(sK1),y) != y }),
    clause({ r(skx1) == r(x3), f(r(skx1),x4) != x5 }),
    btd));
  // normal match
  ASS(tester.eq(
    clause({ r(sK1) == r(x), f(r(sK1),y) != z }),
    clause({ r(skx1) == r(x3), f(r(skx1),x4) != x5 }),
    btd));
}

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
      .input( clause({  f(sK1,skx0) != g(sK1) }))
      .expected(none())
    )

// normal case sik=one
TEST_GENERATION_INDUCTION(test_04,
    Generation::TestCase()
      .options({ { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  ~p(f(sK1,sK2)) }))
      .expected({
        clause({ ~p(f(b,sK2)), p(f(skx0,sK2)) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(skx0),sK2)) }),
        clause({ ~p(f(sK1,b)), p(f(sK1,skx1)) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(skx1))) }),
      })
    )

// normal case sik=two
TEST_GENERATION_INDUCTION(test_05,
    Generation::TestCase()
      .options({ { "induction", "struct" }, { "structural_induction_kind", "two" } })
      .indices({ comparisonIndex() })
      .input( clause({  ~p(f(sK1,sK2)) }))
      .expected({
        clause({ skx0 != r(r0(skx0)), p(f(r0(skx0),sK2)) }),
        clause({ ~p(f(skx0,sK2)) }),
        clause({ skx1 != r(r0(skx1)), p(f(sK1,r0(skx1))) }),
        clause({ ~p(f(sK1,skx1)) }),
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
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(skx0),f(sK2,sK4)),sK1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(r(skx0)),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,sK3))) }),

        // sK1 010
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),skx1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),r(skx1)) != g(f(sK1,f(sK2,sK3))) }),

        // sK1 001
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) == g(f(skx2,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(r(skx2),f(sK2,sK3))) }),

        // sK1 110
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(skx3),f(sK2,sK4)),skx3) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(sK1,f(sK2,sK3))), f(f(g(r(skx3)),f(sK2,sK4)),r(skx3)) != g(f(sK1,f(sK2,sK3))) }),

        // sK1 101
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(skx4),f(sK2,sK4)),sK1) == g(f(skx4,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),sK1) != g(f(b,f(sK2,sK3))), f(f(g(r(skx4)),f(sK2,sK4)),sK1) != g(f(r(skx4),f(sK2,sK3))) }),

        // sK1 011
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),skx5) == g(f(skx5,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(sK1),f(sK2,sK4)),r(skx5)) != g(f(r(skx5),f(sK2,sK3))) }),

        // sK1 111
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(skx6),f(sK2,sK4)),skx6) == g(f(skx6,f(sK2,sK3))) }),
        clause({ f(f(g(b),f(sK2,sK4)),b) != g(f(b,f(sK2,sK3))), f(f(g(r(skx6)),f(sK2,sK4)),r(skx6)) != g(f(r(skx6),f(sK2,sK3))) }),

        // sK2 10
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(skx7,sK4)),sK1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(r(skx7),sK4)),sK1) != g(f(sK1,f(sK2,sK3))) }),

        // sK2 01
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) == g(f(sK1,f(skx8,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(r(skx8),sK3))) }),

        // sK2 11
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(skx9,sK4)),sK1) == g(f(sK1,f(skx9,sK3))) }),
        clause({ f(f(g(sK1),f(b,sK4)),sK1) != g(f(sK1,f(b,sK3))), f(f(g(sK1),f(r(skx9),sK4)),sK1) != g(f(sK1,f(r(skx9),sK3))) }),

        // sK3 1
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,b))), f(f(g(sK1),f(sK2,sK4)),sK1) == g(f(sK1,f(sK2,skx10))) }),
        clause({ f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,b))), f(f(g(sK1),f(sK2,sK4)),sK1) != g(f(sK1,f(sK2,r(skx10)))) }),

        // sK4 1
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,skx11)),sK1) == g(f(sK1,f(sK2,sK3))) }),
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,sK3))), f(f(g(sK1),f(sK2,r(skx11))),sK1) != g(f(sK1,f(sK2,sK3))) }),
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
        clause({ f(f(g(b),f(sK2,sK3)),b) != g(f(b,f(sK2,g(b)))), f(f(g(skx0),f(sK2,sK3)),skx0) == g(f(skx0,f(sK2,g(skx0)))) }),
        clause({ f(f(g(b),f(sK2,sK3)),b) != g(f(b,f(sK2,g(b)))), f(f(g(r(skx0)),f(sK2,sK3)),r(skx0)) != g(f(r(skx0),f(sK2,g(r(skx0))))) }),

        // sK2
        clause({ f(f(g(sK1),f(b,sK3)),sK1) != g(f(sK1,f(b,g(sK1)))), f(f(g(sK1),f(skx1,sK3)),sK1) == g(f(sK1,f(skx1,g(sK1)))) }),
        clause({ f(f(g(sK1),f(b,sK3)),sK1) != g(f(sK1,f(b,g(sK1)))), f(f(g(sK1),f(r(skx1),sK3)),sK1) != g(f(sK1,f(r(skx1),g(sK1)))) }),

        // sK3
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),f(sK2,skx3)),sK1) == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ f(f(g(sK1),f(sK2,b)),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),f(sK2,r(skx3))),sK1) != g(f(sK1,f(sK2,g(sK1)))) }),

        // g(sK1)
        clause({ f(f(b,f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,b))), f(f(skx4,f(sK2,sK3)),sK1) == g(f(sK1,f(sK2,skx4))) }),
        clause({ f(f(b,f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,b))), f(f(r(skx4),f(sK2,sK3)),sK1) != g(f(sK1,f(sK2,r(skx4)))) }),

        // f(sK2,sK3)
        clause({ f(f(g(sK1),b),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),skx5),sK1) == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ f(f(g(sK1),b),sK1) != g(f(sK1,f(sK2,g(sK1)))), f(f(g(sK1),r(skx5)),sK1) != g(f(sK1,f(sK2,g(sK1)))) }),

        // f(g(sK1),f(sK2,sK3))
        clause({ f(b,sK1) != g(f(sK1,f(sK2,g(sK1)))), f(skx6,sK1) == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ f(b,sK1) != g(f(sK1,f(sK2,g(sK1)))), f(r(skx6),sK1) != g(f(sK1,f(sK2,g(sK1)))) }),

        // f(f(g(sK1),f(sK2,sK3)),sK1)
        clause({ b != g(f(sK1,f(sK2,g(sK1)))), skx7 == g(f(sK1,f(sK2,g(sK1)))) }),
        clause({ b != g(f(sK1,f(sK2,g(sK1)))), r(skx7) != g(f(sK1,f(sK2,g(sK1)))) }),

        // f(sK2,g(sK1))
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,b)), f(f(g(sK1),f(sK2,sK3)),sK1) == g(f(sK1,skx8)) }),
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,b)), f(f(g(sK1),f(sK2,sK3)),sK1) != g(f(sK1,r(skx8))) }),

        // f(sK1,f(sK2,g(sK1)))
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(b), f(f(g(sK1),f(sK2,sK3)),sK1) == g(skx9) }),
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != g(b), f(f(g(sK1),f(sK2,sK3)),sK1) != g(r(skx9)) }),

        // g(f(sK1,f(sK2,g(sK1))))
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != b, f(f(g(sK1),f(sK2,sK3)),sK1) == skx10 }),
        clause({ f(f(g(sK1),f(sK2,sK3)),sK1) != b, f(f(g(sK1),f(sK2,sK3)),sK1) != r(skx10) }),
      })
    )

// positive literals are considered 1
TEST_GENERATION_INDUCTION(test_09,
    Generation::TestCase()
      .options({ { "induction_neg_only", "off" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  p(sK1) }))
      .expected({
        clause({ p(b), ~p(skx0), }),
        clause({ p(b), p(r(skx0)), }),
      })
    )

// positive literals are considered 2
TEST_GENERATION_INDUCTION(test_10,
    Generation::TestCase()
      .options({ { "induction_neg_only", "off" }, { "induction", "struct" } })
      .indices({ comparisonIndex() })
      .input( clause({  sK1 == g(sK1) }))
      .expected({
        clause({ b == g(b), skx0 != g(skx0), }),
        clause({ b == g(b), r(skx0) == g(r(skx0)), }),
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
        clause({ b != g(b), skx0 == g(skx0), p(g(sK2)), ~p(f(sK1,sK2)) }),
        clause({ b != g(b), r(skx0) != g(r(skx0)), p(g(sK2)), ~p(f(sK1,sK2)) }),

        // 3. literal sK1
        clause({ ~p(f(b,sK2)), p(f(skx1,sK2)), p(g(sK2)), sK1 != g(sK1) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(skx1),sK2)), p(g(sK2)), sK1 != g(sK1) }),

        // 3. literal sK2
        clause({ ~p(f(sK1,b)), p(f(sK1,skx2)), p(g(sK2)), sK1 != g(sK1) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(skx2))), p(g(sK2)), sK1 != g(sK1) }),
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
        clause({ b != g(b), skx0 == g(skx0), sK2 != g(sK2) }),
        clause({ b != g(b), r(skx0) != g(r(skx0)), sK2 != g(sK2) }),
      })
    )

TEST_GENERATION_INDUCTION(test_13,
    Generation::TestCase()
      .options({ { "induction", "int" } })
      .context({ clause({ ~(sK6 < num(1)) }) })
      .indices({ comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        clause({ ~pi(1), ~(skx0 < num(1)) }),
        clause({ ~pi(1), pi(skx0) }),
        clause({ ~pi(1), ~pi(skx0+1) }),
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
        clause({ ~pi(1), ~(skx0 < num(1)) }),
        clause({ ~pi(1), pi(skx0) }),
        clause({ ~pi(1), ~pi(skx0+1) }),

        // downard induction
        clause({ ~pi(bi), ~(bi < skx1) }),
        clause({ ~pi(bi), pi(skx1) }),
        clause({ ~pi(bi), ~pi(skx1+num(-1)) }),
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
        clause({ ~pi(1), ~(skx0 < num(1)) }),
        clause({ ~pi(1), skx0 < bi }),
        clause({ ~pi(1), pi(skx0) }),
        clause({ ~pi(1), ~pi(skx0+1) }),

        // downard induction
        clause({ ~pi(bi), num(1) < skx1 }),
        clause({ ~pi(bi), ~(bi < skx1) }),
        clause({ ~pi(bi), pi(skx1) }),
        clause({ ~pi(bi), ~pi(skx1+num(-1)) }),
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
        clause({ ~pi(0), ~(skx0 < num(0)) }),
        clause({ ~pi(0), pi(skx0) }),
        clause({ ~pi(0), ~pi(skx0+1) }),

        // downward induction: resulting clauses contain "0 < sK6",
        // since there is no bound to resolve it against
        clause({ ~pi(0), ~(num(0) < skx1), 0 < sK6 }),
        clause({ ~pi(0), pi(skx1), 0 < sK6 }),
        clause({ ~pi(0), ~pi(skx1+num(-1)), 0 < sK6 }),
      })
    )

// all skolems are replaced when the hypothesis strengthening options is on, sik=one
TEST_GENERATION_INDUCTION(test_17,
    Generation::TestCase()
      .options({ { "induction", "struct" },
                 { "induction_strengthen_hypothesis", "on" } })
      .indices({ comparisonIndex() })
      .input( clause({ f(sK1,sK2) != g(sK3) }) )
      .expected({
        // sK1
        clause({ f(b,skx0) != g(skx1), f(skx2,x) == g(y) }),
        clause({ f(b,skx0) != g(skx1), f(r(skx2),skx3) != g(skx4) }),

        // sK2
        clause({ f(skx5,b) != g(skx6), f(z,skx7) == g(x3) }),
        clause({ f(skx5,b) != g(skx6), f(skx8,r(skx7)) != g(skx9) }),

        // sK3
        clause({ f(skx10,skx11) != g(b), f(x4,x5) == g(skx12) }),
        clause({ f(skx10,skx11) != g(b), f(skx13,skx14) != g(r(skx12)) }),
      })
    )

// all skolems are replaced when the hypothesis strengthening options is on, sik=two
TEST_GENERATION_INDUCTION(test_18,
    Generation::TestCase()
      .options({ { "induction", "struct" }, { "structural_induction_kind", "two" },
                 { "induction_strengthen_hypothesis", "on" } })
      .indices({ comparisonIndex() })
      .input( clause({ f(sK1,sK2) != g(sK3) }) )
      .expected({
        // sK1
        clause({ skx0 != r(r0(skx0)), f(r0(skx0),x) == g(y) }),
        clause({ f(skx0,skx1) != g(skx2) }),

        // sK2
        clause({ skx3 != r(r0(skx3)), f(z,r0(skx3)) == g(x3) }),
        clause({ f(skx4,skx3) != g(skx5) }),

        // sK3
        clause({ skx6 != r(r0(skx6)), f(x4,x5) == g(r0(skx6)) }),
        clause({ f(skx7,skx8) != g(skx6) }),
      })
    )
