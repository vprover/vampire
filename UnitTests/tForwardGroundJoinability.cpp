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
#include "Test/MockedSaturationAlgorithm.hpp"

#include "Indexing/CodeTreeInterfaces.hpp"

#include "Inferences/ForwardGroundJoinability.hpp"

#define MY_SYNTAX_SUGAR          \
  DECL_DEFAULT_VARS              \
  DECL_VAR(u, 3)                 \
  DECL_SORT(srt)                 \
  DECL_FUNC (f, {srt, srt}, srt)

TermIndex<DemodulatorData>* demodulationLhsIndex(const SaturationAlgorithm& salg) {
  return new DemodulationLHSIndex(new CodeTreeTIS<DemodulatorData>(), salg.getOrdering(), salg.getOptions());
}

Clause* axiomC() {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  return clause({ f(x,y) == f(y,x) });
}

Clause* axiomA() {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  return clause({ f(f(x,y),z) == f(x,f(y,z)) });
}

Clause* axiomD() {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  return clause({ f(x,f(y,z)) == f(y,f(x,z)) });
}

Clause* axiomM() {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  return clause({ f(x,f(y,z)) == f(z,f(y,x)) });
}

Clause* axiomS() {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);
  return clause({ f(x,f(y,z)) == f(y,f(z,x)) });
}

ClauseStack acdAxioms() {
  return { axiomA(), axiomC(), axiomD() };
}

ClauseStack acmAxioms() {
  return { axiomA(), axiomC(), axiomM() };
}

ClauseStack acsAxioms() {
  return { axiomA(), axiomC(), axiomS() };
}

void joinabilityTest(ClauseStack axioms, Clause* cl, bool joinable, bool useKbo) {

  // set up saturation algorithm
  auto container = PlainClauseContainer();

  // init problem
  Problem p;
  auto ul = UnitList::empty();
  UnitList::pushFromIterator(ClauseStack::ConstRefIterator(axioms), ul);
  p.addUnits(ul);
  env.setMainProblem(&p);

  Options o;
  o.set("term_ordering", useKbo ? "kbo" : "lpo");
  env.options->set("term_ordering", useKbo ? "kbo" : "lpo");
  Test::MockedSaturationAlgorithm salg(p, o);
  const Stack<Index*>& indices = { demodulationLhsIndex(salg) };

  ForwardGroundJoinability fgj;
  fgj.setTestIndices(indices);
  fgj.InferenceEngine::attach(&salg);
  for (auto i : indices) {
    i->attachContainer(&container);
  }

  // add the clauses to the index
  for (auto c : axioms) {
    c->setStore(Clause::ACTIVE);
    container.add(c);
  }

  ClauseIterator replacements;
  ClauseIterator premises;
  Clause* replacement = nullptr;

  ASS_EQ(fgj.perform(cl, replacement, premises), joinable);
  ASS(!replacement);

  // tear down saturation algorithm
  fgj.InferenceEngine::detach();
}

#define TEST_AC_KBO_JOINABLE(name, cl, axioms)                 \
  TEST_FUN(joinable_ac_kbo_##name) {                           \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    auto ax = axioms; /* this forces the evaluation order */   \
    joinabilityTest(ax, cl, true, true);                       \
  }

#define TEST_AC_KBO_NONJOINABLE(name, cl, axioms)              \
  TEST_FUN(nonjoinable_ac_kbo_##name) {                        \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    auto ax = axioms; /* this forces the evaluation order */   \
    joinabilityTest(ax, cl, false, true);                      \
  }

#define TEST_AC_LPO_JOINABLE(name, cl, axioms)                 \
  TEST_FUN(joinable_ac_lpo_##name) {                           \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    auto ax = axioms; /* this forces the evaluation order */   \
    joinabilityTest(ax, cl, true, false);                      \
  }

#define TEST_AC_LPO_NONJOINABLE(name, cl, axioms)              \
  TEST_FUN(nonjoinable_ac_lpo_##name) {                        \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    auto ax = axioms; /* this forces the evaluation order */   \
    joinabilityTest(ax, cl, false, false);                     \
  }

// KBO

// all of these should be joinable by ACD axioms

TEST_AC_KBO_JOINABLE(join2, axiomA(), acdAxioms());

TEST_AC_KBO_JOINABLE(join3_1, clause({ f(f(x,y),z) == f(f(x,y),z) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_2, clause({ f(f(x,y),z) == f(f(x,z),y) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_3, clause({ f(f(x,y),z) == f(f(y,x),z) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_4, clause({ f(f(x,y),z) == f(f(y,z),x) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_5, clause({ f(f(x,y),z) == f(f(z,x),y) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_6, clause({ f(f(x,y),z) == f(f(z,y),x) }), acdAxioms());

TEST_AC_KBO_JOINABLE(join3_7, clause({ f(f(x,y),z) == f(x,f(y,z)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_8, clause({ f(f(x,y),z) == f(x,f(z,y)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_9, clause({ f(f(x,y),z) == f(y,f(x,z)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_10, clause({ f(f(x,y),z) == f(y,f(z,x)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_11, clause({ f(f(x,y),z) == f(z,f(x,y)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_12, clause({ f(f(x,y),z) == f(z,f(y,x)) }), acdAxioms());

TEST_AC_KBO_JOINABLE(join3_13, clause({ f(x,f(y,z)) == f(f(x,y),z) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_14, clause({ f(x,f(y,z)) == f(f(x,z),y) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_15, clause({ f(x,f(y,z)) == f(f(y,x),z) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_16, clause({ f(x,f(y,z)) == f(f(y,z),x) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_17, clause({ f(x,f(y,z)) == f(f(z,x),y) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_18, clause({ f(x,f(y,z)) == f(f(z,y),x) }), acdAxioms());

TEST_AC_KBO_JOINABLE(join3_19, clause({ f(x,f(y,z)) == f(x,f(y,z)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_20, clause({ f(x,f(y,z)) == f(x,f(z,y)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_21, clause({ f(x,f(y,z)) == f(y,f(x,z)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_22, clause({ f(x,f(y,z)) == f(y,f(z,x)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_23, clause({ f(x,f(y,z)) == f(z,f(x,y)) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join3_24, clause({ f(x,f(y,z)) == f(z,f(y,x)) }), acdAxioms());

TEST_AC_KBO_JOINABLE(join4_1, clause({ f(x,f(y,f(z,u))) == f(z,f(x,f(y,u))) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join4_2, clause({ f(x,f(y,f(z,u))) == f(u,f(x,f(y,z))) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join4_3, clause({ f(x,f(y,f(z,u))) == f(z,f(y,f(x,u))) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join4_4, clause({ f(x,f(y,f(z,u))) == f(z,f(u,f(y,x))) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join4_5, clause({ f(y,f(x,f(z,u))) == f(u,f(x,f(y,z))) }), acdAxioms());
TEST_AC_KBO_JOINABLE(join4_6, clause({ f(x,f(y,f(z,u))) == f(y,f(z,f(u,x))) }), acdAxioms());

// D should be joinable by ACM and ACS

// TEST_AC_KBO_JOINABLE(join_d_1, axiomD(), acmAxioms());
TEST_AC_KBO_JOINABLE(join_d_2, axiomD(), acsAxioms());

// each axiom in ACD should not be joinable by the other two

TEST_AC_KBO_NONJOINABLE(nonjoin1, axiomA(), ClauseStack({ axiomC(), axiomD() }));
TEST_AC_KBO_NONJOINABLE(nonjoin2, axiomC(), ClauseStack({ axiomA(), axiomD() }));
TEST_AC_KBO_NONJOINABLE(nonjoin3, axiomD(), ClauseStack({ axiomA(), axiomC() }));

// LPO

// all of these should be joinable by ACD axioms

TEST_AC_LPO_JOINABLE(join2, axiomA(), acdAxioms());

TEST_AC_LPO_JOINABLE(join3_1, clause({ f(f(x,y),z) == f(f(x,y),z) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_2, clause({ f(f(x,y),z) == f(f(x,z),y) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_3, clause({ f(f(x,y),z) == f(f(y,x),z) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_4, clause({ f(f(x,y),z) == f(f(y,z),x) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_5, clause({ f(f(x,y),z) == f(f(z,x),y) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_6, clause({ f(f(x,y),z) == f(f(z,y),x) }), acdAxioms());

TEST_AC_LPO_JOINABLE(join3_7, clause({ f(f(x,y),z) == f(x,f(y,z)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_8, clause({ f(f(x,y),z) == f(x,f(z,y)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_9, clause({ f(f(x,y),z) == f(y,f(x,z)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_10, clause({ f(f(x,y),z) == f(y,f(z,x)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_11, clause({ f(f(x,y),z) == f(z,f(x,y)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_12, clause({ f(f(x,y),z) == f(z,f(y,x)) }), acdAxioms());

TEST_AC_LPO_JOINABLE(join3_13, clause({ f(x,f(y,z)) == f(f(x,y),z) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_14, clause({ f(x,f(y,z)) == f(f(x,z),y) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_15, clause({ f(x,f(y,z)) == f(f(y,x),z) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_16, clause({ f(x,f(y,z)) == f(f(y,z),x) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_17, clause({ f(x,f(y,z)) == f(f(z,x),y) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_18, clause({ f(x,f(y,z)) == f(f(z,y),x) }), acdAxioms());

TEST_AC_LPO_JOINABLE(join3_19, clause({ f(x,f(y,z)) == f(x,f(y,z)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_20, clause({ f(x,f(y,z)) == f(x,f(z,y)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_21, clause({ f(x,f(y,z)) == f(y,f(x,z)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_22, clause({ f(x,f(y,z)) == f(y,f(z,x)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_23, clause({ f(x,f(y,z)) == f(z,f(x,y)) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join3_24, clause({ f(x,f(y,z)) == f(z,f(y,x)) }), acdAxioms());

TEST_AC_LPO_JOINABLE(join4_1, clause({ f(x,f(y,f(z,u))) == f(z,f(x,f(y,u))) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join4_2, clause({ f(x,f(y,f(z,u))) == f(u,f(x,f(y,z))) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join4_3, clause({ f(x,f(y,f(z,u))) == f(z,f(y,f(x,u))) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join4_4, clause({ f(x,f(y,f(z,u))) == f(z,f(u,f(y,x))) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join4_5, clause({ f(y,f(x,f(z,u))) == f(u,f(x,f(y,z))) }), acdAxioms());
TEST_AC_LPO_JOINABLE(join4_6, clause({ f(x,f(y,f(z,u))) == f(y,f(z,f(u,x))) }), acdAxioms());

// D should be joinable by ACM and ACS

// TEST_AC_LPO_JOINABLE(join_d_1, axiomD(), acmAxioms());
// TEST_AC_LPO_JOINABLE(join_d_2, axiomD(), acsAxioms());

// each axiom in ACD should not be joinable by the other two

TEST_AC_LPO_NONJOINABLE(nonjoin1, axiomA(), ClauseStack({ axiomC(), axiomD() }));
TEST_AC_LPO_NONJOINABLE(nonjoin2, axiomC(), ClauseStack({ axiomA(), axiomD() }));
TEST_AC_LPO_NONJOINABLE(nonjoin3, axiomD(), ClauseStack({ axiomA(), axiomC() }));
