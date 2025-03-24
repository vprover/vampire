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

#include "Inferences/ForwardGroundJoinability.hpp"

#define MY_SYNTAX_SUGAR          \
  DECL_DEFAULT_VARS              \
  DECL_VAR(u, 3)                 \
  DECL_SORT(srt)                 \
  DECL_FUNC (f, {srt, srt}, srt)

TermIndex<DemodulatorData>* demodulationLhsIndex(const SaturationAlgorithm& salg) {
  return new DemodulationLHSIndex(new CodeTreeTIS<DemodulatorData>(), salg.getOrdering(), salg.getOptions());
}

ClauseStack acAxioms() {
  __ALLOW_UNUSED(MY_SYNTAX_SUGAR);

  return {
    clause({ f(x,y) == f(y,x) }),
    clause({ f(f(x,y),z) == f(x,f(y,z)) }),
    clause({ f(x,f(y,z)) == f(y,f(x,z)) }),
  };
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

  ForwardGroundJoinability fgj(o);
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

  ASS_EQ(fgj.perform(cl, premises), joinable);

  // tear down saturation algorithm
  fgj.InferenceEngine::detach();
}

#define TEST_AC_KBO_JOINABLE(name, cl)                         \
  TEST_FUN(joinable_ac_kbo_##name) {                           \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    joinabilityTest(acAxioms(), clause({ cl }), true, true);   \
  }

#define TEST_AC_KBO_NONJOINABLE(name, cl)                      \
  TEST_FUN(nonjoinable_ac_kbo_##name) {                        \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    joinabilityTest(acAxioms(), clause({ cl }), false, true);  \
  }

#define TEST_AC_LPO_JOINABLE(name, cl)                         \
  TEST_FUN(joinable_ac_lpo_##name) {                           \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    joinabilityTest(acAxioms(), clause({ cl }), true, false);  \
  }

#define TEST_AC_LPO_NONJOINABLE(name, cl)                      \
  TEST_FUN(nonjoinable_ac_lpo_##name) {                        \
    __ALLOW_UNUSED(MY_SYNTAX_SUGAR);                           \
    joinabilityTest(acAxioms(), clause({ cl }), false, false); \
  }

// KBO

TEST_AC_KBO_JOINABLE(base1, f(x,y) == f(y,x));
TEST_AC_KBO_JOINABLE(base2, f(f(x,y),z) == f(x,f(y,z)));
TEST_AC_KBO_JOINABLE(base3, f(x,f(y,z)) == f(y,f(x,z)));

TEST_AC_KBO_JOINABLE(join1, f(f(x,y),z) == f(f(x,y),z));
TEST_AC_KBO_JOINABLE(join2, f(f(x,y),z) == f(f(x,z),y));
TEST_AC_KBO_JOINABLE(join3, f(f(x,y),z) == f(f(y,x),z));
TEST_AC_KBO_JOINABLE(join4, f(f(x,y),z) == f(f(y,z),x));
TEST_AC_KBO_JOINABLE(join5, f(f(x,y),z) == f(f(z,x),y));
TEST_AC_KBO_JOINABLE(join6, f(f(x,y),z) == f(f(z,y),x));

TEST_AC_KBO_JOINABLE(join7, f(f(x,y),z) == f(x,f(z,y)));
TEST_AC_KBO_JOINABLE(join8, f(f(x,y),z) == f(y,f(x,z)));
TEST_AC_KBO_JOINABLE(join9, f(f(x,y),z) == f(y,f(z,x)));
TEST_AC_KBO_JOINABLE(join10, f(f(x,y),z) == f(z,f(x,y)));
TEST_AC_KBO_JOINABLE(join11, f(f(x,y),z) == f(z,f(y,x)));

TEST_AC_KBO_JOINABLE(join12, f(x,f(y,z)) == f(f(x,y),z));
TEST_AC_KBO_JOINABLE(join13, f(x,f(y,z)) == f(f(x,z),y));
TEST_AC_KBO_JOINABLE(join14, f(x,f(y,z)) == f(f(y,x),z));
TEST_AC_KBO_JOINABLE(join15, f(x,f(y,z)) == f(f(y,z),x));
TEST_AC_KBO_JOINABLE(join16, f(x,f(y,z)) == f(f(z,x),y));
TEST_AC_KBO_JOINABLE(join17, f(x,f(y,z)) == f(f(z,y),x));

TEST_AC_KBO_JOINABLE(join18, f(x,f(y,z)) == f(x,f(y,z)));
TEST_AC_KBO_JOINABLE(join19, f(x,f(y,z)) == f(x,f(z,y)));
TEST_AC_KBO_JOINABLE(join20, f(x,f(y,z)) == f(y,f(z,x)));
TEST_AC_KBO_JOINABLE(join21, f(x,f(y,z)) == f(z,f(x,y)));
TEST_AC_KBO_JOINABLE(join22, f(x,f(y,z)) == f(z,f(y,x)));

TEST_AC_KBO_JOINABLE(join23, f(x,f(y,f(z,u))) == f(z,f(x,f(y,u))));
TEST_AC_KBO_JOINABLE(join24, f(x,f(y,f(z,u))) == f(u,f(x,f(y,z))));
TEST_AC_KBO_JOINABLE(join25, f(x,f(y,f(z,u))) == f(z,f(y,f(x,u))));
TEST_AC_KBO_JOINABLE(join26, f(x,f(y,f(z,u))) == f(z,f(u,f(y,x))));
TEST_AC_KBO_JOINABLE(join27, f(y,f(x,f(z,u))) == f(u,f(x,f(y,z))));
TEST_AC_KBO_JOINABLE(join28, f(x,f(y,f(z,u))) == f(y,f(z,f(u,x))));

// LPO

TEST_AC_LPO_JOINABLE(base1, f(x,y) == f(y,x));
TEST_AC_LPO_JOINABLE(base2, f(f(x,y),z) == f(x,f(y,z)));
TEST_AC_LPO_JOINABLE(base3, f(x,f(y,z)) == f(y,f(x,z)));

TEST_AC_LPO_JOINABLE(join1, f(f(x,y),z) == f(f(x,y),z));
TEST_AC_LPO_JOINABLE(join2, f(f(x,y),z) == f(f(x,z),y));
TEST_AC_LPO_JOINABLE(join3, f(f(x,y),z) == f(f(y,x),z));
TEST_AC_LPO_JOINABLE(join4, f(f(x,y),z) == f(f(y,z),x));
TEST_AC_LPO_JOINABLE(join5, f(f(x,y),z) == f(f(z,x),y));
TEST_AC_LPO_JOINABLE(join6, f(f(x,y),z) == f(f(z,y),x));

TEST_AC_LPO_JOINABLE(join7, f(f(x,y),z) == f(x,f(z,y)));
TEST_AC_LPO_JOINABLE(join8, f(f(x,y),z) == f(y,f(x,z)));
TEST_AC_LPO_JOINABLE(join9, f(f(x,y),z) == f(y,f(z,x)));
TEST_AC_LPO_JOINABLE(join10, f(f(x,y),z) == f(z,f(x,y)));
TEST_AC_LPO_JOINABLE(join11, f(f(x,y),z) == f(z,f(y,x)));

TEST_AC_LPO_JOINABLE(join12, f(x,f(y,z)) == f(f(x,y),z));
TEST_AC_LPO_JOINABLE(join13, f(x,f(y,z)) == f(f(x,z),y));
TEST_AC_LPO_JOINABLE(join14, f(x,f(y,z)) == f(f(y,x),z));
TEST_AC_LPO_JOINABLE(join15, f(x,f(y,z)) == f(f(y,z),x));
TEST_AC_LPO_JOINABLE(join16, f(x,f(y,z)) == f(f(z,x),y));
TEST_AC_LPO_JOINABLE(join17, f(x,f(y,z)) == f(f(z,y),x));

TEST_AC_LPO_JOINABLE(join18, f(x,f(y,z)) == f(x,f(y,z)));
TEST_AC_LPO_JOINABLE(join19, f(x,f(y,z)) == f(x,f(z,y)));
TEST_AC_LPO_JOINABLE(join20, f(x,f(y,z)) == f(y,f(z,x)));
TEST_AC_LPO_JOINABLE(join21, f(x,f(y,z)) == f(z,f(x,y)));
TEST_AC_LPO_JOINABLE(join22, f(x,f(y,z)) == f(z,f(y,x)));

TEST_AC_LPO_JOINABLE(join23, f(x,f(y,f(z,u))) == f(z,f(x,f(y,u))));
TEST_AC_LPO_JOINABLE(join24, f(x,f(y,f(z,u))) == f(u,f(x,f(y,z))));
TEST_AC_LPO_JOINABLE(join25, f(x,f(y,f(z,u))) == f(z,f(y,f(x,u))));
TEST_AC_LPO_JOINABLE(join26, f(x,f(y,f(z,u))) == f(z,f(u,f(y,x))));
TEST_AC_LPO_JOINABLE(join27, f(y,f(x,f(z,u))) == f(u,f(x,f(y,z))));
TEST_AC_LPO_JOINABLE(join28, f(x,f(y,f(z,u))) == f(y,f(z,f(u,x))));
