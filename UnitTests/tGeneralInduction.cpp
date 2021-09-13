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

#include "Indexing/LiteralIndex.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Indexing/TermIndex.hpp"

#include "Inferences/GeneralInduction.hpp"

using namespace Test;
using namespace Test::Generation;

vvector<InductionSchemeGenerator*> generators() {
  return { new StructuralInductionSchemeGenerator(), new IntegerInductionSchemeGenerator() };
}

TermIndex* index() {
  return new DemodulationSubtermIndexImpl<false>(new TermSubstitutionTree(false, false));
}

LiteralIndex* comparisonIndex() {
  return new UnitIntegerComparisonLiteralIndex(new LiteralSubstitutionTree());
}

template<class Rule>
class GenerationTesterInduction
  : public GenerationTester<Rule>
{
public:
  GenerationTesterInduction(Rule* rule)
    : GenerationTester<Rule>(rule), _subst()
  {}

  bool eq(Kernel::Clause const* lhs, Kernel::Clause const* rhs) override
  {
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
    GenerationTesterInduction<GeneralInduction> tester(                                                       \
      new GeneralInduction(generators()));                                                                    \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR)                                                                           \
    auto test = __VA_ARGS__;                                                                                  \
    test.run(tester);                                                                                         \
  }                                                                                                           \

/**
 * NECESSARY: We neet to tell the tester which syntax sugar to import for creating terms & clauses. 
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
  DECL_SKOLEM_CONST(sK6, Int)                                                              \
  DECL_CONST(bi, Int)

// induction info is added 1
TEST_GENERATION_INDUCTION(test_01,
    Generation::TestCase()
      .indices({ index() })
      .input( clause({  ~p(f(sK1,sK2)) }))
      .expected({
        clause({ ~p(f(b,sK2)), p(f(x,sK2)) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(x),sK2)) }),
        clause({ ~p(f(sK1,b)), p(f(sK1,y)) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(y))) }),
      })
      .all([](Clause* c) {
        return c->inference().inductionInfo() && !c->inference().inductionInfo()->isEmpty();
      })
    )

// induction info is added 2
TEST_GENERATION_INDUCTION(test_02,
    Generation::TestCase()
      .indices({ index() })
      .input( clause({  f(sK1,sK2) != g(sK1) }))
      .expected({
        clause({ f(b,sK2) != g(b), f(x,sK2) == g(x) }),
        clause({ f(b,sK2) != g(b), f(r(x),sK2) != g(r(x)) }),
        clause({ f(sK1,b) != g(sK1), f(sK1,y) == g(sK1) }),
        clause({ f(sK1,b) != g(sK1), f(sK1,r(y)) != g(sK1) }),
      })
      .all([](Clause* c) {
        return c->inference().inductionInfo() && !c->inference().inductionInfo()->isEmpty();
      })
    )

// induction info is not added 1
TEST_GENERATION_INDUCTION(test_03,
    Generation::TestCase()
      .indices({ index() })
      .options({ { "induction_multiclause", "off" } })
      .input( clause({  ~p(f(sK1,sK2)) }))
      .expected({
        clause({ ~p(f(b,sK2)), p(f(x,sK2)) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(x),sK2)) }),
        clause({ ~p(f(sK1,b)), p(f(sK1,y)) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(y))) }),
      })
      .all([](Clause* c) {
        return !c->inference().inductionInfo();
      })
    )

// induction info is not added 2
TEST_GENERATION_INDUCTION(test_04,
    Generation::TestCase()
      .indices({ index() })
      .options({ { "induction_hypothesis_rewriting", "off" } })
      .input( clause({  f(sK1,sK2) != g(sK1) }))
      .expected({
        clause({ f(b,sK2) != g(b), f(x,sK2) == g(x) }),
        clause({ f(b,sK2) != g(b), f(r(x),sK2) != g(r(x)) }),
        clause({ f(sK1,b) != g(sK1), f(sK1,y) == g(sK1) }),
        clause({ f(sK1,b) != g(sK1), f(sK1,r(y)) != g(sK1) }),
      })
      .all([](Clause* c) {
        return !c->inference().inductionInfo();
      })
    )

// positive literals are not considered 1
TEST_GENERATION_INDUCTION(test_05,
    Generation::TestCase()
      .indices({ index() })
      .input( clause({  p(f(sK1,sK2)) }))
      .expected(none())
    )

// positive literals are not considered 2
TEST_GENERATION_INDUCTION(test_06,
    Generation::TestCase()
      .indices({ index() })
      .input( clause({  f(sK1,sK2) == g(sK1) }))
      .expected(none())
    )

// multi-clause use case 1 (induction depth 0 for all literals)
TEST_GENERATION_INDUCTION(test_07,
    Generation::TestCase()
      .context({ clause({ p(sK1) })})
      .indices({ index() })
      .input( clause({ sK2 != g(f(sK1,sK1)) }))
      .expected({
        // formula 1
        clause({ b != g(f(sK1,sK1)), x == g(f(sK1,sK1)) }),
        clause({ b != g(f(sK1,sK1)), r(x) != g(f(sK1,sK1)) }),

        // formula 2
        clause({ sK2 != g(f(b,b)), sK2 == g(f(y,y)), ~p(y) }),
        clause({ sK2 != g(f(b,b)), p(r(y)) }),
        clause({ sK2 != g(f(b,b)), sK2 != g(f(r(y),r(y))) }),
        clause({ p(b), sK2 == g(f(y,y)), ~p(y) }),
        clause({ p(b), p(r(y)) }),
        clause({ p(b), sK2 != g(f(r(y),r(y))) }),
      })
    )

// multi-clause use case 2 (induction Skolems and  for all literals)
TEST_GENERATION_INDUCTION(test_08,
    Generation::TestCase()
      .options({ { "induction_on_complex_terms", "on" } })
      .context({ fromInduction(clause({ p(g(sK3)) })) })
      .indices({ index() })
      .input( fromInduction(clause({ ~p(f(g(sK3),sK4)) })) )
      .expected({
        // formula 1
        clause({ ~p(f(b,sK4)), p(f(x,sK4)), ~p(x) }),
        clause({ ~p(f(b,sK4)), ~p(f(r(x),sK4)) }),
        clause({ ~p(f(b,sK4)), p(r(x)) }),
        clause({ p(b), p(f(x,sK4)), ~p(x) }),
        clause({ p(b), ~p(f(r(x),sK4)) }),
        clause({ p(b), p(r(x)) }),

        // formula 2
        clause({ ~p(f(g(b),sK4)), p(f(g(y),sK4)) }),
        clause({ ~p(f(g(b),sK4)), ~p(f(g(r(y)),sK4)) }),

        // formula 3
        clause({ ~p(f(g(sK3),b)), p(f(g(sK3),z)) }),
        clause({ ~p(f(g(sK3),b)), ~p(f(g(sK3),r(z))) }),

        // formula 4
        clause({ ~p(b), p(x3) }),
        clause({ ~p(b), ~p(r(x3)) }),
      })
    )

// generalizations (single-clause)
TEST_GENERATION_INDUCTION(test_09,
    Generation::TestCase()
      .options({ { "induction_gen", "on" }, { "induction_gen_heur", "off" }, })
      .indices({ index() })
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

// generalizations (multi-clause)
TEST_GENERATION_INDUCTION(test_10,
    Generation::TestCase()
      .options({ { "induction_gen", "on" }, { "induction_gen_heur", "off" }, })
      .context({ clause({ g(sK3) == f(sK4,sK3) }) })
      .indices({ index() })
      .input( clause({ ~p(f(g(sK3),f(sK3,sK4))) }) )
      .expected({
        // sK3 10 10
        clause({ ~p(f(g(b),f(sK3,sK4))), g(x) != f(sK4,sK3), p(f(g(x),f(sK3,sK4))) }),
        clause({ ~p(f(g(b),f(sK3,sK4))), g(r(x)) == f(sK4,sK3) }),
        clause({ ~p(f(g(b),f(sK3,sK4))), ~p(f(g(r(x)),f(sK3,sK4))) }),
        clause({ g(b) == f(sK4,sK3), g(x) != f(sK4,sK3), p(f(g(x),f(sK3,sK4))) }),
        clause({ g(b) == f(sK4,sK3), g(r(x)) == f(sK4,sK3) }),
        clause({ g(b) == f(sK4,sK3), ~p(f(g(r(x)),f(sK3,sK4))) }),

        // sK3 10 01
        clause({ ~p(f(g(b),f(sK3,sK4))), g(sK3) != f(sK4,x7), p(f(g(x7),f(sK3,sK4))) }),
        clause({ ~p(f(g(b),f(sK3,sK4))), g(sK3) == f(sK4,r(x7)) }),
        clause({ ~p(f(g(b),f(sK3,sK4))), ~p(f(g(r(x7)),f(sK3,sK4))) }),
        clause({ g(sK3) == f(sK4,b), g(sK3) != f(sK4,x7), p(f(g(x7),f(sK3,sK4))) }),
        clause({ g(sK3) == f(sK4,b), g(sK3) == f(sK4,r(x7)) }),
        clause({ g(sK3) == f(sK4,b), ~p(f(g(r(x7)),f(sK3,sK4))) }),

        // sK3 10 11
        clause({ ~p(f(g(b),f(sK3,sK4))), g(z) != f(sK4,z), p(f(g(z),f(sK3,sK4))) }),
        clause({ ~p(f(g(b),f(sK3,sK4))), g(r(z)) == f(sK4,r(z)) }),
        clause({ ~p(f(g(b),f(sK3,sK4))), ~p(f(g(r(z)),f(sK3,sK4))) }),
        clause({ g(b) == f(sK4,b), g(z) != f(sK4,z), p(f(g(z),f(sK3,sK4))) }),
        clause({ g(b) == f(sK4,b), g(r(z)) == f(sK4,r(z)) }),
        clause({ g(b) == f(sK4,b), ~p(f(g(r(z)),f(sK3,sK4))) }),

        // sK3 01 10
        clause({ ~p(f(g(sK3),f(b,sK4))), g(x5) != f(sK4,sK3), p(f(g(sK3),f(x5,sK4))) }),
        clause({ ~p(f(g(sK3),f(b,sK4))), g(r(x5)) == f(sK4,sK3) }),
        clause({ ~p(f(g(sK3),f(b,sK4))), ~p(f(g(sK3),f(r(x5),sK4))) }),
        clause({ g(b) == f(sK4,sK3), g(x5) != f(sK4,sK3), p(f(g(sK3),f(x5,sK4))) }),
        clause({ g(b) == f(sK4,sK3), g(r(x5)) == f(sK4,sK3) }),
        clause({ g(b) == f(sK4,sK3), ~p(f(g(sK3),f(r(x5),sK4))) }),

        // sK3 01 01
        clause({ ~p(f(g(sK3),f(b,sK4))), g(sK3) != f(sK4,x8), p(f(g(sK3),f(x8,sK4))) }),
        clause({ ~p(f(g(sK3),f(b,sK4))), g(sK3) == f(sK4,r(x8)) }),
        clause({ ~p(f(g(sK3),f(b,sK4))), ~p(f(g(sK3),f(r(x8),sK4))) }),
        clause({ g(sK3) == f(sK4,b), g(sK3) != f(sK4,x8), p(f(g(sK3),f(x8,sK4))) }),
        clause({ g(sK3) == f(sK4,b), g(sK3) == f(sK4,r(x8)) }),
        clause({ g(sK3) == f(sK4,b), ~p(f(g(sK3),f(r(x8),sK4))) }),

        // sK3 01 11
        clause({ ~p(f(g(sK3),f(b,sK4))), g(x9) != f(sK4,x9), p(f(g(sK3),f(x9,sK4))) }),
        clause({ ~p(f(g(sK3),f(b,sK4))), g(r(x9)) == f(sK4,r(x9)) }),
        clause({ ~p(f(g(sK3),f(b,sK4))), ~p(f(g(sK3),f(r(x9),sK4))) }),
        clause({ g(b) == f(sK4,b), g(x9) != f(sK4,x9), p(f(g(sK3),f(x9,sK4))) }),
        clause({ g(b) == f(sK4,b), g(r(x9)) == f(sK4,r(x9)) }),
        clause({ g(b) == f(sK4,b), ~p(f(g(sK3),f(r(x9),sK4))) }),

        // sK3 11 10
        clause({ ~p(f(g(b),f(b,sK4))), g(y) != f(sK4,sK3), p(f(g(y),f(y,sK4))) }),
        clause({ ~p(f(g(b),f(b,sK4))), g(r(y)) == f(sK4,sK3) }),
        clause({ ~p(f(g(b),f(b,sK4))), ~p(f(g(r(y)),f(r(y),sK4))) }),
        clause({ g(b) == f(sK4,sK3), g(y) != f(sK4,sK3), p(f(g(y),f(y,sK4))) }),
        clause({ g(b) == f(sK4,sK3), g(r(y)) == f(sK4,sK3) }),
        clause({ g(b) == f(sK4,sK3), ~p(f(g(r(y)),f(r(y),sK4))) }),

        // sK3 11 01
        clause({ ~p(f(g(b),f(b,sK4))), g(sK3) != f(sK4,x6), p(f(g(x6),f(x6,sK4))) }),
        clause({ ~p(f(g(b),f(b,sK4))), g(sK3) == f(sK4,r(x6)) }),
        clause({ ~p(f(g(b),f(b,sK4))), ~p(f(g(r(x6)),f(r(x6),sK4))) }),
        clause({ g(sK3) == f(sK4,b), g(sK3) != f(sK4,x6), p(f(g(x6),f(x6,sK4))) }),
        clause({ g(sK3) == f(sK4,b), g(sK3) == f(sK4,r(x6)) }),
        clause({ g(sK3) == f(sK4,b), ~p(f(g(r(x6)),f(r(x6),sK4))) }),

        // sK3 11 11
        clause({ ~p(f(g(b),f(b,sK4))), g(x3) != f(sK4,x3), p(f(g(x3),f(x3,sK4))) }),
        clause({ ~p(f(g(b),f(b,sK4))), g(r(x3)) == f(sK4,r(x3)) }),
        clause({ ~p(f(g(b),f(b,sK4))), ~p(f(g(r(x3)),f(r(x3),sK4))) }),
        clause({ g(b) == f(sK4,b), g(x3) != f(sK4,x3), p(f(g(x3),f(x3,sK4))) }),
        clause({ g(b) == f(sK4,b), g(r(x3)) == f(sK4,r(x3)) }),
        clause({ g(b) == f(sK4,b), ~p(f(g(r(x3)),f(r(x3),sK4))) }),

        // sK4 1 1
        clause({ ~p(f(g(sK3),f(sK3,b))), g(sK3) != f(x4,sK3), p(f(g(sK3),f(sK3,x4))) }),
        clause({ ~p(f(g(sK3),f(sK3,b))), g(sK3) == f(r(x4),sK3) }),
        clause({ ~p(f(g(sK3),f(sK3,b))), ~p(f(g(sK3),f(sK3,r(x4)))) }),
        clause({ g(sK3) == f(b,sK3), g(sK3) != f(x4,sK3), p(f(g(sK3),f(sK3,x4))) }),
        clause({ g(sK3) == f(b,sK3), g(sK3) == f(r(x4),sK3) }),
        clause({ g(sK3) == f(b,sK3), ~p(f(g(sK3),f(sK3,r(x4)))) }),
      })
    )

// side premise triggers multi-clause
TEST_GENERATION_INDUCTION(test_11,
    Generation::TestCase()
      .context({ clause({ ~p(f(sK1,sK2)) }),
                 clause({ p(sK2) }) })
      .indices({ index() })
      .input( clause({ p(sK1) }))
      .expected({
        clause({ p(b), ~p(x), p(f(x,sK2)) }),
        clause({ p(b), p(r(x)) }),
        clause({ p(b), ~p(f(r(x),sK2)) }),
        clause({ ~p(f(b,sK2)), ~p(x), p(f(x,sK2)) }),
        clause({ ~p(f(b,sK2)), p(r(x)) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(x),sK2)) }),
      })
    )

// multi-clause does not work due to clauses
// being from different induction depths
TEST_GENERATION_INDUCTION(test_12,
    Generation::TestCase()
      .context({ fromInduction(clause({ p(sK1) })) })
      .indices({ index() })
      .input( clause({ ~p(g(sK1)) }))
      .expected({
        clause({ ~p(g(b)), p(g(x)) }),
        clause({ ~p(g(b)), ~p(g(r(x))) }),
      })
    )

// multi-clause does not work due to clauses
// not having complex terms in common
TEST_GENERATION_INDUCTION(test_13,
    Generation::TestCase()
      .options({ { "induction_on_complex_terms", "on" } })
      .context({ fromInduction(clause({ p(sK1) })) })
      .indices({ index() })
      .input( fromInduction(clause({ ~p(g(sK1)) })) )
      .expected({
        clause({ ~p(g(b)), p(g(x)) }),
        clause({ ~p(g(b)), ~p(g(r(x))) }),

        clause({ ~p(b), p(y) }),
        clause({ ~p(b), ~p(r(y)) }),
      })
    )

// multiple induction hypotheses and cases
TEST_GENERATION_INDUCTION(test_14,
    Generation::TestCase()
      .indices({ index() })
      .input( fromInduction(clause({ ~q(sK5) })) )
      .expected({
        clause({ ~q(b1), ~q(b2), ~q(r1(x,y,z)), ~q(r2(x3,x4)) }),
        clause({ ~q(b1), ~q(b2), q(y), ~q(r2(x3,x4)) }),
        clause({ ~q(b1), ~q(b2), q(z), ~q(r2(x3,x4)) }),
        clause({ ~q(b1), ~q(b2), ~q(r1(x,y,z)), q(x3) }),
        clause({ ~q(b1), ~q(b2), q(y), q(x3) }),
        clause({ ~q(b1), ~q(b2), q(z), q(x3) }),
      })
    )

// side premise queries main premise only once
TEST_GENERATION_INDUCTION(test_17,
    Generation::TestCase()
      .context({ clause({ ~p(f(sK1,sK2)) }) })
      .indices({ index() })
      .input( clause({ p(f(sK2,sK1)) }))
      .expected({
        // formula 1
        clause({ p(f(b,sK1)), ~p(f(y,sK1)), p(f(sK1,y)) }),
        clause({ p(f(b,sK1)), p(f(r(y),sK1)) }),
        clause({ p(f(b,sK1)), ~p(f(sK1,r(y))) }),
        clause({ ~p(f(sK1,b)), ~p(f(y,sK1)), p(f(sK1,y)) }),
        clause({ ~p(f(sK1,b)), p(f(r(y),sK1)) }),
        clause({ ~p(f(sK1,b)), ~p(f(sK1,r(y))) }),

        // formula 2
        clause({ p(f(sK2,b)), ~p(f(sK2,x)), p(f(x,sK2)) }),
        clause({ p(f(sK2,b)), p(f(sK2,r(x))) }),
        clause({ p(f(sK2,b)), ~p(f(r(x),sK2)) }),
        clause({ ~p(f(b,sK2)), ~p(f(sK2,x)), p(f(x,sK2)) }),
        clause({ ~p(f(b,sK2)), p(f(sK2,r(x))) }),
        clause({ ~p(f(b,sK2)), ~p(f(r(x),sK2)) }),
      })
    )

// side literal does not trigger induction 1 (inequal induction depth)
TEST_GENERATION_INDUCTION(test_18,
    Generation::TestCase()
      .context({ fromInduction(clause({ ~p(g(g(sK1))) })) })
      .indices({ index() })
      .input( clause({ p(g(sK1)) }))
      .expected(none())
    )

// side literal does not trigger induction 2 (no shared complex term)
TEST_GENERATION_INDUCTION(test_19,
    Generation::TestCase()
      .context({ fromInduction(clause({ ~p(g(sK1)) })) })
      .indices({ index() })
      .input( fromInduction(clause({ p(f(sK1,sK1)) })) )
      .expected(none())
    )

// complementary literals should not cause any problems
TEST_GENERATION_INDUCTION(test_20,
    Generation::TestCase()
      .context({ clause({ p(sK1) }) })
      .indices({ index() })
      .input( clause({ ~p(sK1) }))
      .expected({
        // formula 1
        clause({ p(b), ~p(x), p(x) }),
        clause({ p(b), p(r(x)) }),
        clause({ p(b), ~p(r(x)) }),
        clause({ ~p(b), ~p(x), p(x) }),
        clause({ ~p(b), p(r(x)) }),
        clause({ ~p(b), ~p(r(x)) }),
      })
    )

// bounds are used for integer induction even when multi-clause is off 
// (strictness 0 means that the bound is eligible as a side as well)
TEST_GENERATION_INDUCTION(test_21,
    Generation::TestCase()
      .options({ { "induction_multiclause", "off" }, { "induction", "int" }, { "int_induction_strictness", "0" } })
      .context({ clause({ ~(sK6 < num(1)) }) })
      .indices({ index(), comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        clause({ ~pi(1), ~(x < num(1)) }),
        clause({ ~pi(1), pi(x) }),
        clause({ ~pi(1), ~pi(x+1) }),
      })
    )

// use bounds for upward+downward infinite interval integer induction
TEST_GENERATION_INDUCTION(test_22,
    Generation::TestCase()
      .options({ { "induction_multiclause", "off" }, { "induction", "int" }, { "int_induction_interval", "infinite" } })
      .context({ clause({ ~(sK6 < num(1)) }), clause({ ~(bi < sK6) }) })
      .indices({ index(), comparisonIndex() })
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
TEST_GENERATION_INDUCTION(test_23,
    Generation::TestCase()
      .options({ { "induction_multiclause", "off" }, { "induction", "int" }, { "int_induction_interval", "finite" } })
      .context({ clause({ ~(sK6 < num(1)) }), clause({ ~(bi < sK6) }) })
      .indices({ index(), comparisonIndex() })
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
TEST_GENERATION_INDUCTION(test_24,
    Generation::TestCase()
      .options({ { "induction_multiclause", "off" },
                 { "induction", "int" },
                 { "int_induction_interval", "infinite" },
                 { "int_induction_default_bound", "on" } })
      .context({ clause({ ~(sK6 < num(0)) }) })
      .indices({ index(), comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        // upward induction
        clause({ ~pi(0), ~(x < num(0)) }),
        clause({ ~pi(0), pi(x) }),
        clause({ ~pi(0), ~pi(x+1) }),

        // downard induction: resulting clauses contain "0 < sK6",
        // since there is no bound to resolve it against
        clause({ ~pi(0), ~(num(0) < y), 0 < sK6 }),
        clause({ ~pi(0), pi(y), 0 < sK6 }),
        clause({ ~pi(0), ~pi(y+num(-1)), 0 < sK6 }),
      })
    )
    
// as previous test, but use two default bounds for finite integer induction
TEST_GENERATION_INDUCTION(test_25,
    Generation::TestCase()
      .options({ { "induction_multiclause", "off" },
                 { "induction", "int" },
                 { "int_induction_interval", "finite" },
                 { "int_induction_default_bound", "on" },
                 { "int_induction_second_default_bound", "on" } })
      .context({ clause({ ~(sK6 < num(0)) }) })
      .indices({ index(), comparisonIndex() })
      .input( clause({ ~pi(sK6) }) )
      .expected({
        // upward induction
        clause({ ~pi(0), ~(x < num(0)), sK6 < sK6 }),
        clause({ ~pi(0), x < sK6, sK6 < sK6 }),
        clause({ ~pi(0), pi(x), sK6 < sK6 }),
        clause({ ~pi(0), ~pi(x+1), sK6 < sK6 }),

        // downard induction: resulting clauses contain "0 < sK6",
        // since there is no bound to resolve it against
        clause({ ~pi(0), ~(num(0) < y), 0 < sK6, sK6 < sK6 }),
        clause({ ~pi(0), sK6 < y, 0 < sK6, sK6 < sK6 }),
        clause({ ~pi(0), pi(y), 0 < sK6, sK6 < sK6 }),
        clause({ ~pi(0), ~pi(y+num(-1)), 0 < sK6, sK6 < sK6 }),
      })
    )
