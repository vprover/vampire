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

#include "Inferences/GeneralInduction.hpp"

using namespace Test;
using namespace Test::Generation;

vvector<InductionSchemeGenerator*> generators() {
  return { new StructuralInductionSchemeGenerator() };
}

TermIndex* index() {
  return new DemodulationSubtermIndexImpl<false>(new TermSubstitutionTree(false, false));
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
    return TestUtils::permEq(*lhs, *rhs, [this](Literal* l, Literal* r) -> bool {
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
    });
  }

private:
  Kernel::RobSubstitution _subst;
};

#define TEST_GENERATION_INDUCTION(name, ...)                                                                  \
  TEST_FUN(name) {                                                                                            \
    GenerationTesterInduction<GeneralInduction> tester(                                                       \
      new GeneralInduction(generators(), InferenceRule::INDUCTION_AXIOM));                                    \
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
  DECL_SORT(s)                                                                             \
  DECL_SKOLEM_CONST(sK1, s)                                                                \
  DECL_SKOLEM_CONST(sK2, s)                                                                \
  DECL_INDUCTION_SKOLEM_CONST(sK3, s)                                                      \
  DECL_INDUCTION_SKOLEM_CONST(sK4, s)                                                      \
  DECL_CONST(b, s)                                                                         \
  DECL_FUNC(r, {s}, s)                                                                     \
  DECL_TERM_ALGEBRA(s, {b, r})                                                             \
  DECL_FUNC(f, {s, s}, s)                                                                  \
  DECL_FUNC(g, {s}, s)                                                                     \
  DECL_PRED(p, {s})

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
