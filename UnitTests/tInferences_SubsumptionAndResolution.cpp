/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include <fstream>

#include "Test/SyntaxSugar.hpp"
#include "Inferences/ForwardSubsumptionAndResolution.hpp"
#include "Inferences/BackwardSubsumptionAndResolution.hpp"
#include "Indexing/ClauseCodeTree.hpp"

#include "Test/FwdBwdSimplificationTester.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Indexing;
using namespace Test;

#define MY_SYNTAX_SUGAR  \
 __ALLOW_UNUSED( \
    DECL_DEFAULT_VARS \
    DECL_SORT(s) \
    DECL_VAR_SORTED(x1, 1, s) \
    DECL_VAR_SORTED(x2, 2, s) \
    DECL_VAR_SORTED(x3, 3, s) \
    DECL_VAR_SORTED(x4, 4, s) \
    DECL_VAR_SORTED(x5, 5, s) \
    DECL_VAR_SORTED(x6, 6, s) \
    DECL_VAR_SORTED(x7, 7, s) \
    DECL_VAR_SORTED(x8, 8, s) \
    DECL_VAR_SORTED(x9, 9, s) \
    DECL_VAR_SORTED(x10, 10, s) \
    DECL_VAR_SORTED(x11, 11, s) \
    DECL_VAR_SORTED(x12, 12, s) \
    DECL_VAR_SORTED(y1, 21, s) \
    DECL_VAR_SORTED(y2, 22, s) \
    DECL_VAR_SORTED(y3, 23, s) \
    DECL_VAR_SORTED(y4, 24, s) \
    DECL_VAR_SORTED(y5, 25, s) \
    DECL_VAR_SORTED(y6, 26, s) \
    DECL_VAR_SORTED(y7, 27, s) \
    DECL_CONST(c, s) \
    DECL_CONST(d, s) \
    DECL_CONST(e, s) \
    DECL_FUNC(f, {s}, s) \
    DECL_FUNC(f2, {s, s}, s) \
    DECL_FUNC(f3, {s, s, s}, s) \
    DECL_FUNC(g, {s}, s) \
    DECL_FUNC(g2, {s, s}, s) \
    DECL_FUNC(h, {s}, s) \
    DECL_FUNC(h2, {s, s}, s) \
    DECL_FUNC(i, {s}, s) \
    DECL_FUNC(i2, {s, s}, s) \
    DECL_FUNC(sum, {s, s}, s) \
    DECL_FUNC(underlying_curve, {s}, s) \
    DECL_FUNC(sK1, {s, s}, s) \
    DECL_FUNC(sK2, {s, s}, s) \
    DECL_FUNC(sK3, {s, s}, s) \
    DECL_FUNC(sK4, {s, s}, s) \
    DECL_FUNC(sK5, {s, s, s, s}, s) \
    DECL_FUNC(sK6, {s, s}, s) \
    DECL_FUNC(sK7, {s}, s) \
    DECL_FUNC(sK8, {s, s, s, s}, s) \
    DECL_CONST(sK9, s) \
    DECL_CONST(sK10, s) \
    DECL_CONST(sK11, s) \
    DECL_CONST(sK12, s) \
    DECL_CONST(sK13, s) \
    DECL_CONST(skc8, s) \
    DECL_CONST(skc9, s) \
    DECL_CONST(skc10, s) \
    DECL_CONST(skc11, s) \
    DECL_CONST(skc12, s) \
    DECL_CONST(skc13, s) \
    DECL_CONST(skc14, s) \
    DECL_CONST(skc15, s) \
    DECL_FUNC(sK14, {s}, s) \
    DECL_FUNC(sK15, {s}, s) \
    DECL_FUNC(sK16, {s, s}, s) \
    DECL_FUNC(sK17, {s, s}, s) \
    DECL_FUNC(sK18, {s, s, s}, s) \
    DECL_FUNC(sK19, {s, s}, s) \
    DECL_FUNC(sK20, {s, s}, s) \
    DECL_FUNC(sK21, {s, s}, s) \
    DECL_FUNC(sK22, {s, s}, s) \
    DECL_FUNC(sK23, {s, s}, s) \
    DECL_FUNC(sK24, {s}, s) \
    DECL_FUNC(sK25, {s, s, s}, s) \
    DECL_FUNC(sK26, {s, s}, s) \
    DECL_FUNC(sK27, {s}, s) \
    DECL_FUNC(skf1, {s}, s) \
    DECL_PRED(p, {s}) \
    DECL_PRED(p2, {s, s}) \
    DECL_PRED(p3, {s, s, s}) \
    DECL_PRED(q, {s}) \
    DECL_PRED(q2, {s, s}) \
    DECL_PRED(r, {s}) \
    DECL_PRED(r2, {s, s}) \
    DECL_PRED(between, {s, s, s, s}) \
    DECL_PRED(between_c, {s, s, s, s}) \
    DECL_PRED(between_o, {s, s, s, s}) \
    DECL_PRED(closed, {s}) \
    DECL_PRED(end_point, {s, s}) \
    DECL_PRED(finish_point, {s, s}) \
    DECL_PRED(incident_c, {s, s}) \
    DECL_PRED(incident_o, {s, s}) \
    DECL_PRED(inner_point, {s, s}) \
    DECL_PRED(meet, {s, s, s}) \
    DECL_PRED(open, {s}) \
    DECL_PRED(ordered_by, {s, s, s}) \
    DECL_PRED(part_of, {s, s}) \
    DECL_PRED(sP0, {s, s, s, s, s}) \
    DECL_PRED(start_point, {s, s}) \
    DECL_PRED(abstraction, {s, s}) \
    DECL_PRED(accessible_world, {s, s}) \
    DECL_PRED(agent, {s, s, s}) \
    DECL_PRED(animate, {s, s}) \
    DECL_PRED(be, {s, s, s, s}) \
    DECL_PRED(entity, {s, s}) \
    DECL_PRED(event, {s, s}) \
    DECL_PRED(eventuality, {s, s}) \
    DECL_PRED(existent, {s, s}) \
    DECL_PRED(forename, {s, s}) \
    DECL_PRED(general, {s, s}) \
    DECL_PRED(human, {s, s}) \
    DECL_PRED(human_person, {s, s}) \
    DECL_PRED(impartial, {s, s}) \
    DECL_PRED(jules_forename, {s, s}) \
    DECL_PRED(living, {s, s}) \
    DECL_PRED(male, {s, s}) \
    DECL_PRED(man, {s, s}) \
    DECL_PRED(nonexistent, {s, s}) \
    DECL_PRED(nonhuman, {s, s}) \
    DECL_PRED(of, {s, s, s}) \
    DECL_PRED(organism, {s, s}) \
    DECL_PRED(present, {s, s}) \
    DECL_PRED(proposition, {s, s}) \
    DECL_PRED(relation, {s, s}) \
    DECL_PRED(relname, {s, s}) \
    DECL_PRED(singleton, {s, s}) \
    DECL_PRED(smoke, {s, s}) \
    DECL_PRED(specific, {s, s}) \
    DECL_PRED(state, {s, s}) \
    DECL_PRED(theme, {s, s, s}) \
    DECL_PRED(thing, {s, s}) \
    DECL_PRED(think_believe_consider, {s, s}) \
    DECL_PRED(unisex, {s, s}) \
    DECL_PRED(vincent_forename, {s, s}) \
  )

namespace {

inline auto tester() {
  return FwdBwdSimplification::TestCase<
      ForwardSubsumptionAndResolution,
      BackwardSubsumptionAndResolution</*higherOrder=*/false>
    >()
    .options({
      { "backward_subsumption", "on" },
      { "backward_subsumption_resolution", "on" }
    });
}

// Note: most of these tests were taken from the SAT subsumption test suite

// positive subsumptions

TEST_SIMPLIFICATION(pos_sub_test01,
  tester()
    .simplifyWith({ clause({ p2(x, f(y)) }) })
    .toSimplify({ clause({ p2(c, f(d)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test02,
  tester()
    .simplifyWith({ clause({ ~p2(g(x), f(y)) }) })
    .toSimplify({ clause({ ~p2(g(x), f(x)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test03,
  tester()
    .simplifyWith({ clause({ p3(x1, x2, x3), p3(f(x2), x4, x4) }) })
    .toSimplify({ clause({ p3(f(c), d, y1), p3(f(d), c, c) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test04,
  tester()
    .simplifyWith({ clause({ p3(x1, x2, x3), p3(f(x2), x4, x4) }) })
    .toSimplify({ clause({ p3(f(c), d, y1), p3(f(d), c, c), r(x1) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test05,
  tester()
    .simplifyWith({ clause({ p(f2(f(g(x1)), x1)), c == g(x1) }) })
    .toSimplify({ clause({ g(y1) == c, p(f2(f(g(y1)), y1)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test06,
  tester()
    .simplifyWith({ clause({ f2(x1, x2) == c, ~p2(x1, x3), p2(f(f2(x1, x2)), f(x3)) }) })
    .toSimplify({ clause({ c == f2(x3, y2), ~p2(x3, y1), p2(f(f2(x3, y2)), f(y1)) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test07,
  tester()
    .simplifyWith({ clause({ p(f2(f(e), g2(x4, x3))), p2(f2(f(e), g2(x4, x3)), x3), f(e) == g2(x4, x3) }) })
    .toSimplify({ clause({ p(f2(f(e), g2(y1, y3))), p2(f2(f(e), g2(y1, y3)), y3), f(e) == g2(y1, y3) }) })
    .expected({ /* nothing */ })
)

TEST_SIMPLIFICATION(pos_sub_test08,
  tester()
    .simplifyWith({ clause({ p3(y7, f(y1), x4), ~p3(y7, y1, x4) }) })
    .toSimplify({ clause({ p3(x6, f(y3), d), ~p3(x6, y3, d) }) })
    .expected({ /* nothing */ })
)

// negative subsumptions

TEST_SIMPLIFICATION(neg_sub_test01,
  tester()
    .simplifyWith({ clause({ p2(f2(g2(x1, x2), x3), x3), p2(f2(g2(x1, x2), x3), x2), g2(x1, x2) == x3 }) })
    .toSimplify({ clause({ p2(f2(g2(y1, y2), y2), y2), g2(y1, y2) == y2, ~p2(f2(g2(y1, y2), y2), g2(y1, y2)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test02,
  tester()
    .simplifyWith({ clause({ ~p2(x1, x2), p(x1) }) })
    .toSimplify({ clause({ p(y1), ~p(f(f2(f2(y2, y2), f2(y2, y3)))), ~p(y3), ~p(y2) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test03,
  tester()
    .simplifyWith({ clause({ p2(y5, f(f2(c, x1))), ~p(c), ~p(y5) }) })
    .toSimplify({ clause({ ~q(f(d)), p2(c, f(f2(c, x4))), r(e), ~p(c), d == g(c) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test04,
  tester()
    .simplifyWith({ clause({ p2(y5, f(f2(x1, c))), ~p(c), ~p(y5) }) })
    .toSimplify({ clause({ ~q(d), p2(c, f(f2(x4, c))), r(d), ~p(c), d == g(c) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test05,
  tester()
    .simplifyWith({ clause({ p(x1), x1 == f(x2), p(x2) }) })
    .toSimplify({ clause({ p(y1), y1 == f(y1) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test06,
  tester()
    .simplifyWith({ clause({ p(x1), x1 == f(x2), p(x2), q(x1) }) })
    .toSimplify({ clause({ p(y1), y1 == f(y1), q(y2), r(y3) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_test07,
  tester()
    .simplifyWith({ clause({ p(f(x1)), p(f(x2)) }) })
    .toSimplify({ clause({ p(f(y1)), p(g(y2)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

// positive subsumption resolutions

TEST_SIMPLIFICATION(pos_sub_res_test01,
  tester()
    .simplifyWith({ clause({ ~p(x1), q(x1) }) })
    .toSimplify({ clause({ p(c), q(c), r(e) }) })
    .expected({ clause({ q(c), r(e) }) })
)

TEST_SIMPLIFICATION(pos_sub_res_test02,
  tester()
    .simplifyWith({ clause({ p2(x1, x2), p2(f(x2), x3) }) })
    .toSimplify({ clause({ ~p2(f(y1), d), p2(g(y1), c), ~p2(f(c), e) }) })
    .expected({ clause({ ~p2(f(y1), d), p2(g(y1), c) }) })
)

TEST_SIMPLIFICATION(pos_sub_res_test03,
  tester()
    .simplifyWith({ clause({ p3(x2, f(x2), e) }) })
    .toSimplify({ clause({ p3(f(e), x5, x5), ~p3(x4, f(x4), e) }) })
    .expected({ clause({ p3(f(e), x5, x5) }) })
)

TEST_SIMPLIFICATION(pos_sub_res_test04,
  tester()
    .simplifyWith({ clause({ p(c) }) })
    .toSimplify({ clause({ ~p(c) }) })
    .expected({ clause({}) })
)

TEST_SIMPLIFICATION(pos_sub_res_test05,
  tester()
    .simplifyWith({ clause({ ~p(f(x1)), q(x1) }) })
    .toSimplify({ clause({ ~p2(x2, x5), q(x2), p(f(x2)), ~q(g(x5)) }) })
    .expected({ clause({ ~p2(x2, x5), q(x2), ~q(g(x5)) }) })
)

// negative subsumption resolutions

TEST_SIMPLIFICATION(neg_sub_res_test01,
  tester()
    .simplifyWith({ clause({ ~p(x1), q(x1) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test02,
  tester()
    .simplifyWith({ clause({ ~p(x1), ~q(x2) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test03,
  tester()
    .simplifyWith({ clause({ ~p(x1), r(c) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test04,
  tester()
    .simplifyWith({ clause({ ~p(x1), p2(x1, x2) }) })
    .toSimplify({ clause({ p(c), q(d), r(e) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test05,
  tester()
    .simplifyWith({ clause({ p3(x1, x2, x2), ~p3(x2, c, c) }) })
    .toSimplify({ clause({ p3(y1, c, c), ~p3(y1, y2, y2) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test06,
  tester()
    .simplifyWith({ clause({ p3(y7, x6, x6), ~p3(y7, d, d) }) })
    .toSimplify({ clause({ p3(x5, d, d), ~p3(x5, x6, x6) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test07,
  tester()
    .simplifyWith({ clause({ ~p3(y7, d, d), p3(y7, x6, x6) }) })
    .toSimplify({ clause({ ~p3(x5, y4, f(f2(x4, f(y3)))), p3(x2, d, d), ~p3(x7, x4, y3), ~p3(x2, f2(x5, y4), x7) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test08,
  tester()
    .simplifyWith({ clause({ ~p3(y7, d, d), p3(y7, x6, x6) }) })
    .toSimplify({ clause({ ~p3(x5, x6, x6), p3(d, d, x5) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test09,
  tester()
    .simplifyWith({ clause({ ~p3(d, y7, d), p3(x6, y7, x6) }) })
    .toSimplify({ clause({ p3(d, x5, d), ~p3(y4, f(y4), f(x5)) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test10,
  tester()
    .simplifyWith({ clause({ ~p3(d, d, d), p3(f(f(y7)), d, y7) }) })
    .toSimplify({ clause({ p3(d, x6, x6) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test11,
  tester()
    .simplifyWith({ clause({ p2(y7, d), p2(e, y7), e == y7 }) })
    .toSimplify({ clause({ ~p2(x6, x5), ~p2(y7, x6), p2(y7, x5) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_SIMPLIFICATION(neg_sub_res_test12,
  tester()
    .simplifyWith({ clause({ f2(y1, y3) == x1, ~p2(g2(x1, f2(y1, y3)), x1), ~p2(g2(x1, f2(y1, y3)), y1), ~p2(g2(x1, f2(y1, y3)), y3) }) })
    .toSimplify({ clause({ p2(g2(x2, f2(y1, y3)), x2), f2(y1, y3) == x2, p2(g2(x2, f2(y1, y3)), y3) }) })
    .expected({ /* nothing */ })
    .justifications({ /* nothing */ })
)

TEST_FUN(reproducer)
{
  MY_SYNTAX_SUGAR
  ClauseCodeTree<false> wtree;
  ClauseCodeTree<false>::ClauseMatcher m;
  Kernel::Clause* D;
  int resolvedQueryLit;


  Kernel::Clause* C1 = clause({~man(skc12,x1), ~agent(skc12,skf1(x1),x1)});
  wtree.insert(C1);
  D = clause({human_person(x1,x2), organism(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C2 = clause({human_person(x1,x2), organism(x1,x2)});
  wtree.insert(C2);
  D = clause({human(x1,x3), ~human(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C3 = clause({human(x1,x3), ~human(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C3);
  D = clause({general(x1,x3), ~general(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C4 = clause({general(x1,x3), ~general(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C4);
  D = clause({state(x1,x2), ~eventuality(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C5 = clause({state(x1,x2), ~eventuality(x1,x2)});
  wtree.insert(C5);
  D = clause({~state(skc8,skc9)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C6 = clause({~state(skc8,skc9)});
  wtree.insert(C6);
  D = clause({human(x1,x2), ~nonhuman(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C7 = clause({human(x1,x2), ~nonhuman(x1,x2)});
  wtree.insert(C7);
  D = clause({human_person(x1,x3), accessible_world(x1,x2), ~human_person(x2,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C8 = clause({human_person(x1,x3), accessible_world(x1,x2), ~human_person(x2,x3)});
  wtree.insert(C8);
  D = clause({~relname(x1,x2), relation(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C9 = clause({~relname(x1,x2), relation(x1,x2)});
  wtree.insert(C9);
  D = clause({~think_believe_consider(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C10 = clause({~think_believe_consider(skc8,skc13)});
  wtree.insert(C10);
  D = clause({~existent(x2,x3), existent(x1,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C11 = clause({~existent(x2,x3), existent(x1,x3), accessible_world(x1,x2)});
  wtree.insert(C11);
  D = clause({~jules_forename(x1,x2), forename(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C12 = clause({~jules_forename(x1,x2), forename(x1,x2)});
  wtree.insert(C12);
  D = clause({forename(skc8,skc14)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C13 = clause({forename(skc8,skc14)});
  wtree.insert(C13);
  D = clause({man(skc8,skc15)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C14 = clause({man(skc8,skc15)});
  wtree.insert(C14);
  D = clause({~man(x1,x2), ~human_person(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C15 = clause({~man(x1,x2), ~human_person(x1,x2)});
  wtree.insert(C15);
  D = clause({~animate(x1,x3), accessible_world(x1,x2), animate(x2,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C16 = clause({~animate(x1,x3), accessible_world(x1,x2), animate(x2,x3)});
  wtree.insert(C16);
  D = clause({proposition(x1,x2), relation(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C17 = clause({proposition(x1,x2), relation(x1,x2)});
  wtree.insert(C17);
  D = clause({~organism(x1,x2), entity(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C18 = clause({~organism(x1,x2), entity(x1,x2)});
  wtree.insert(C18);
  D = clause({x2 == x3, think_believe_consider(x1,x4), agent(x1,x4,x6), agent(x1,x5,x6), proposition(x1,x2), proposition(x1,x3), theme(x1,x5,x3), theme(x1,x4,x2), think_believe_consider(x1,x5)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C19 = clause({x2 == x3, think_believe_consider(x1,x4), agent(x1,x4,x6), agent(x1,x5,x6), proposition(x1,x2), proposition(x1,x3), theme(x1,x5,x3), theme(x1,x4,x2), think_believe_consider(x1,x5)});
  wtree.insert(C19);
  D = clause({vincent_forename(skc8,skc14)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C20 = clause({vincent_forename(skc8,skc14)});
  wtree.insert(C20);
  D = clause({~agent(skc8,skc13,skc15)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C21 = clause({~agent(skc8,skc13,skc15)});
  wtree.insert(C21);
  D = clause({~man(x1,x2), male(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C22 = clause({~man(x1,x2), male(x1,x2)});
  wtree.insert(C22);
  D = clause({of(skc8,skc14,skc15)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C23 = clause({of(skc8,skc14,skc15)});
  wtree.insert(C23);
  D = clause({~relname(x1,x3), relname(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C24 = clause({~relname(x1,x3), relname(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C24);
  D = clause({~eventuality(x1,x2), event(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C25 = clause({~eventuality(x1,x2), event(x1,x2)});
  wtree.insert(C25);
  D = clause({forename(skc8,skc11)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C26 = clause({forename(skc8,skc11)});
  wtree.insert(C26);
  D = clause({~event(skc12,skf1(x2)), ~man(skc12,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C27 = clause({~event(skc12,skf1(x2)), ~man(skc12,x1)});
  wtree.insert(C27);
  D = clause({~proposition(skc8,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C28 = clause({~proposition(skc8,skc12)});
  wtree.insert(C28);
  D = clause({~forename(x1,x3), accessible_world(x1,x2), forename(x2,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C29 = clause({~forename(x1,x3), accessible_world(x1,x2), forename(x2,x3)});
  wtree.insert(C29);
  D = clause({~general(x1,x2), ~abstraction(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C30 = clause({~general(x1,x2), ~abstraction(x1,x2)});
  wtree.insert(C30);
  D = clause({accessible_world(x1,x2), ~unisex(x1,x3), unisex(x2,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C31 = clause({accessible_world(x1,x2), ~unisex(x1,x3), unisex(x2,x3)});
  wtree.insert(C31);
  D = clause({state(x1,x2), ~event(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C32 = clause({state(x1,x2), ~event(x1,x2)});
  wtree.insert(C32);
  D = clause({human_person(x1,x2), animate(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C33 = clause({human_person(x1,x2), animate(x1,x2)});
  wtree.insert(C33);
  D = clause({vincent_forename(x2,x3), ~vincent_forename(x1,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C34 = clause({vincent_forename(x2,x3), ~vincent_forename(x1,x3), accessible_world(x1,x2)});
  wtree.insert(C34);
  D = clause({eventuality(x1,x2), thing(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C35 = clause({eventuality(x1,x2), thing(x1,x2)});
  wtree.insert(C35);
  D = clause({~accessible_world(skc8,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C36 = clause({~accessible_world(skc8,skc12)});
  wtree.insert(C36);
  D = clause({~present(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C37 = clause({~present(skc8,skc13)});
  wtree.insert(C37);
  D = clause({accessible_world(x1,x2), ~impartial(x2,x3), impartial(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C38 = clause({accessible_world(x1,x2), ~impartial(x2,x3), impartial(x1,x3)});
  wtree.insert(C38);
  D = clause({~forename(x1,x2), relname(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C39 = clause({~forename(x1,x2), relname(x1,x2)});
  wtree.insert(C39);
  D = clause({~relation(x1,x2), abstraction(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C40 = clause({~relation(x1,x2), abstraction(x1,x2)});
  wtree.insert(C40);
  D = clause({x2 == x3, ~forename(x1,x3), ~of(x1,x3,x4), ~of(x1,x2,x4), ~forename(x1,x2), ~entity(x1,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C41 = clause({x2 == x3, ~forename(x1,x3), ~of(x1,x3,x4), ~of(x1,x2,x4), ~forename(x1,x2), ~entity(x1,x4)});
  wtree.insert(C41);
  D = clause({general(x1,x2), ~specific(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C42 = clause({general(x1,x2), ~specific(x1,x2)});
  wtree.insert(C42);
  D = clause({~singleton(x2,x3), singleton(x1,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C43 = clause({~singleton(x2,x3), singleton(x1,x3), accessible_world(x1,x2)});
  wtree.insert(C43);
  D = clause({specific(x1,x2), ~entity(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C44 = clause({specific(x1,x2), ~entity(x1,x2)});
  wtree.insert(C44);
  D = clause({jules_forename(skc8,skc11)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C45 = clause({jules_forename(skc8,skc11)});
  wtree.insert(C45);
  D = clause({~unisex(x1,x2), ~male(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C46 = clause({~unisex(x1,x2), ~male(x1,x2)});
  wtree.insert(C46);
  D = clause({~human(x1,x2), human_person(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C47 = clause({~human(x1,x2), human_person(x1,x2)});
  wtree.insert(C47);
  D = clause({~agent(x2,x3,x4), agent(x1,x3,x4), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C48 = clause({~agent(x2,x3,x4), agent(x1,x3,x4), accessible_world(x1,x2)});
  wtree.insert(C48);
  D = clause({accessible_world(x1,x2), ~eventuality(x2,x3), eventuality(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C49 = clause({accessible_world(x1,x2), ~eventuality(x2,x3), eventuality(x1,x3)});
  wtree.insert(C49);
  D = clause({accessible_world(x1,x2), be(x1,x3,x4,x5), ~be(x2,x3,x4,x5)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C50 = clause({accessible_world(x1,x2), be(x1,x3,x4,x5), ~be(x2,x3,x4,x5)});
  wtree.insert(C50);
  D = clause({~impartial(x1,x2), ~organism(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C51 = clause({~impartial(x1,x2), ~organism(x1,x2)});
  wtree.insert(C51);
  D = clause({think_believe_consider(x1,x3), ~think_believe_consider(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C52 = clause({think_believe_consider(x1,x3), ~think_believe_consider(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C52);
  D = clause({theme(x1,x3,x4), ~theme(x2,x3,x4), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C53 = clause({theme(x1,x3,x4), ~theme(x2,x3,x4), accessible_world(x1,x2)});
  wtree.insert(C53);
  D = clause({man(skc8,skc10)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C54 = clause({man(skc8,skc10)});
  wtree.insert(C54);
  D = clause({relation(x2,x3), accessible_world(x1,x2), ~relation(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C55 = clause({relation(x2,x3), accessible_world(x1,x2), ~relation(x1,x3)});
  wtree.insert(C55);
  D = clause({~specific(x1,x3), specific(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C56 = clause({~specific(x1,x3), specific(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C56);
  D = clause({accessible_world(x1,x2), thing(x2,x3), ~thing(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C57 = clause({accessible_world(x1,x2), thing(x2,x3), ~thing(x1,x3)});
  wtree.insert(C57);
  D = clause({~present(skc12,skf1(x2)), ~man(skc12,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C58 = clause({~present(skc12,skf1(x2)), ~man(skc12,x1)});
  wtree.insert(C58);
  D = clause({entity(x2,x3), accessible_world(x1,x2), ~entity(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C59 = clause({entity(x2,x3), accessible_world(x1,x2), ~entity(x1,x3)});
  wtree.insert(C59);
  D = clause({abstraction(x2,x3), accessible_world(x1,x2), ~abstraction(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C60 = clause({abstraction(x2,x3), accessible_world(x1,x2), ~abstraction(x1,x3)});
  wtree.insert(C60);
  D = clause({~theme(skc8,skc13,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C61 = clause({~theme(skc8,skc13,skc12)});
  wtree.insert(C61);
  D = clause({~existent(x1,x2), ~entity(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C62 = clause({~existent(x1,x2), ~entity(x1,x2)});
  wtree.insert(C62);
  D = clause({living(x1,x3), ~living(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C63 = clause({living(x1,x3), ~living(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C63);
  D = clause({~abstraction(x1,x2), thing(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C64 = clause({~abstraction(x1,x2), thing(x1,x2)});
  wtree.insert(C64);
  D = clause({of(skc8,skc11,skc10)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C65 = clause({of(skc8,skc11,skc10)});
  wtree.insert(C65);
  D = clause({~living(x1,x2), ~organism(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C66 = clause({~living(x1,x2), ~organism(x1,x2)});
  wtree.insert(C66);
  D = clause({accessible_world(x1,x2), ~proposition(x2,x3), proposition(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C67 = clause({accessible_world(x1,x2), ~proposition(x2,x3), proposition(x1,x3)});
  wtree.insert(C67);
  D = clause({thing(x1,x2), ~entity(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C68 = clause({thing(x1,x2), ~entity(x1,x2)});
  wtree.insert(C68);
  D = clause({eventuality(x1,x2), ~nonexistent(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C69 = clause({eventuality(x1,x2), ~nonexistent(x1,x2)});
  wtree.insert(C69);
  D = clause({~event(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C70 = clause({~event(skc8,skc13)});
  wtree.insert(C70);
  D = clause({forename(x1,x2), ~vincent_forename(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C71 = clause({forename(x1,x2), ~vincent_forename(x1,x2)});
  wtree.insert(C71);
  D = clause({accessible_world(x1,x2), organism(x2,x3), ~organism(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C72 = clause({accessible_world(x1,x2), organism(x2,x3), ~organism(x1,x3)});
  wtree.insert(C72);
  D = clause({~abstraction(x1,x2), unisex(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C73 = clause({~abstraction(x1,x2), unisex(x1,x2)});
  wtree.insert(C73);
  D = clause({nonhuman(x1,x2), ~abstraction(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C74 = clause({nonhuman(x1,x2), ~abstraction(x1,x2)});
  wtree.insert(C74);
  D = clause({~state(x2,x3), accessible_world(x1,x2), state(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C75 = clause({~state(x2,x3), accessible_world(x1,x2), state(x1,x3)});
  wtree.insert(C75);
  D = clause({accessible_world(x1,x2), ~smoke(x2,x3), smoke(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C76 = clause({accessible_world(x1,x2), ~smoke(x2,x3), smoke(x1,x3)});
  wtree.insert(C76);
  D = clause({~event(x1,x2), smoke(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C77 = clause({~event(x1,x2), smoke(x1,x2)});
  wtree.insert(C77);
  D = clause({unisex(x1,x2), eventuality(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C78 = clause({unisex(x1,x2), eventuality(x1,x2)});
  wtree.insert(C78);
  D = clause({~event(x2,x3), event(x1,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C79 = clause({~event(x2,x3), event(x1,x3), accessible_world(x1,x2)});
  wtree.insert(C79);
  D = clause({~be(skc8,skc9,skc10,skc10)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C80 = clause({~be(skc8,skc9,skc10,skc10)});
  wtree.insert(C80);
  D = clause({man(x2,x3), ~man(x1,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C81 = clause({man(x2,x3), ~man(x1,x3), accessible_world(x1,x2)});
  wtree.insert(C81);
  D = clause({~jules_forename(x1,x3), jules_forename(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C82 = clause({~jules_forename(x1,x3), jules_forename(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C82);
  D = clause({specific(x1,x2), eventuality(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C83 = clause({specific(x1,x2), eventuality(x1,x2)});
  wtree.insert(C83);
  D = clause({~smoke(skc12,skf1(x2)), ~man(skc12,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C84 = clause({~smoke(skc12,skf1(x2)), ~man(skc12,x1)});
  wtree.insert(C84);
  D = clause({existent(x1,x2), nonexistent(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C85 = clause({existent(x1,x2), nonexistent(x1,x2)});
  wtree.insert(C85);
  D = clause({accessible_world(x1,x2), nonhuman(x2,x3), ~nonhuman(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C86 = clause({accessible_world(x1,x2), nonhuman(x2,x3), ~nonhuman(x1,x3)});
  wtree.insert(C86);
  D = clause({be(x1,x2,x3,x4), x3 == x4});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C87 = clause({be(x1,x2,x3,x4), x3 == x4});
  wtree.insert(C87);
  D = clause({nonexistent(x1,x3), accessible_world(x1,x2), ~nonexistent(x2,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C88 = clause({nonexistent(x1,x3), accessible_world(x1,x2), ~nonexistent(x2,x3)});
  wtree.insert(C88);
  D = clause({~singleton(x1,x2), ~thing(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C89 = clause({~singleton(x1,x2), ~thing(x1,x2)});
  wtree.insert(C89);
  D = clause({~male(x1,x3), male(x2,x3), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C90 = clause({~male(x1,x3), male(x2,x3), accessible_world(x1,x2)});
  wtree.insert(C90);
  D = clause({~present(x2,x3), accessible_world(x1,x2), present(x1,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C91 = clause({~present(x2,x3), accessible_world(x1,x2), present(x1,x3)});
  wtree.insert(C91);
  D = clause({of(x2,x3,x4), ~of(x1,x3,x4), accessible_world(x1,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C92 = clause({of(x2,x3,x4), ~of(x1,x3,x4), accessible_world(x1,x2)});
  wtree.insert(C92);
  wtree.remove(C14);
  D = clause({man(skc8,skc15)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C93 = clause({man(skc8,skc15)});
  wtree.insert(C93);
  wtree.remove(C13);
  D = clause({forename(skc8,skc14)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C94 = clause({forename(skc8,skc14)});
  wtree.insert(C94);
  wtree.remove(C20);
  D = clause({vincent_forename(skc8,skc14)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C95 = clause({vincent_forename(skc8,skc14)});
  wtree.insert(C95);
  wtree.remove(C45);
  D = clause({jules_forename(skc8,skc11)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C96 = clause({jules_forename(skc8,skc11)});
  wtree.insert(C96);
  wtree.remove(C26);
  D = clause({forename(skc8,skc11)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C97 = clause({forename(skc8,skc11)});
  wtree.insert(C97);
  wtree.remove(C54);
  D = clause({man(skc8,skc10)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C98 = clause({man(skc8,skc10)});
  wtree.insert(C98);
  wtree.remove(C70);
  D = clause({~event(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C99 = clause({~event(skc8,skc13)});
  wtree.insert(C99);
  wtree.remove(C37);
  D = clause({~present(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C100 = clause({~present(skc8,skc13)});
  wtree.insert(C100);
  wtree.remove(C36);
  D = clause({~accessible_world(skc8,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C101 = clause({~accessible_world(skc8,skc12)});
  wtree.insert(C101);
  wtree.remove(C28);
  D = clause({~proposition(skc8,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C102 = clause({~proposition(skc8,skc12)});
  wtree.insert(C102);
  wtree.remove(C10);
  D = clause({~think_believe_consider(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C103 = clause({~think_believe_consider(skc8,skc13)});
  wtree.insert(C103);
  wtree.remove(C6);
  D = clause({~state(skc8,skc9)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C104 = clause({~state(skc8,skc9)});
  wtree.insert(C104);
  wtree.remove(C23);
  D = clause({of(skc8,skc14,skc15)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C105 = clause({of(skc8,skc14,skc15)});
  wtree.insert(C105);
  wtree.remove(C65);
  D = clause({of(skc8,skc11,skc10)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C106 = clause({of(skc8,skc11,skc10)});
  wtree.insert(C106);
  wtree.remove(C61);
  D = clause({~theme(skc8,skc13,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C107 = clause({~theme(skc8,skc13,skc12)});
  wtree.insert(C107);
  wtree.remove(C21);
  D = clause({~agent(skc8,skc13,skc15)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C108 = clause({~agent(skc8,skc13,skc15)});
  wtree.insert(C108);
  wtree.remove(C80);
  D = clause({~be(skc8,skc9,skc10,skc10)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C109 = clause({~be(skc8,skc9,skc10,skc10)});
  wtree.insert(C109);
  wtree.remove(C84);
  D = clause({~smoke(skc12,skf1(x2))});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C110 = clause({~smoke(skc12,skf1(x2))});
  wtree.insert(C110);
  wtree.remove(C58);
  D = clause({~man(skc12,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C111 = clause({~man(skc12,x1)});
  wtree.insert(C111);
  wtree.remove(C27);
  D = clause({forename(skc8,skc11)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({forename(skc8,skc14)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({~event(skc12,skf1(x1))});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C112 = clause({~event(skc12,skf1(x1))});
  wtree.insert(C112);
  D = clause({~event(skc8,skc9)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C113 = clause({~event(skc8,skc9)});
  wtree.insert(C113);
  D = clause({~eventuality(skc8,skc13)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C114 = clause({~eventuality(skc8,skc13)});
  wtree.insert(C114);
  D = clause({~eventuality(skc8,skc9)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C115 = clause({~eventuality(skc8,skc9)});
  wtree.insert(C115);
  D = clause({~present(x1,x2), accessible_world(x3,x1), present(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C116 = clause({~present(x1,x2), accessible_world(x3,x1), present(x4,x2), accessible_world(x4,x3)});
  wtree.insert(C116);
  D = clause({~present(x1,skc13), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C117 = clause({~present(x1,skc13), accessible_world(skc8,x1)});
  wtree.insert(C117);
  D = clause({present(x1,x2), accessible_world(x1,x3), ~present(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({~jules_forename(x1,x2), accessible_world(x1,x3), forename(x3,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C118 = clause({~jules_forename(x1,x2), accessible_world(x1,x3), forename(x3,x2)});
  wtree.insert(C118);
  D = clause({~jules_forename(x1,x2), accessible_world(x1,x3), jules_forename(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C119 = clause({~jules_forename(x1,x2), accessible_world(x1,x3), jules_forename(x4,x2), accessible_world(x3,x4)});
  wtree.insert(C119);
  D = clause({jules_forename(x1,x2), accessible_world(x3,x1), ~jules_forename(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({jules_forename(x1,skc11), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C120 = clause({jules_forename(x1,skc11), accessible_world(skc8,x1)});
  wtree.insert(C120);
  D = clause({man(x1,x2), accessible_world(x3,x1), ~man(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C121 = clause({man(x1,x2), accessible_world(x3,x1), ~man(x4,x2), accessible_world(x4,x3)});
  wtree.insert(C121);
  D = clause({man(x1,skc10), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C122 = clause({man(x1,skc10), accessible_world(skc8,x1)});
  wtree.insert(C122);
  D = clause({man(x1,skc15), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C123 = clause({man(x1,skc15), accessible_world(skc8,x1)});
  wtree.insert(C123);
  D = clause({~man(x1,x2), accessible_world(x1,x3), man(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({~man(x1,x2), accessible_world(x1,skc12)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C124 = clause({~man(x1,x2), accessible_world(x1,skc12)});
  wtree.insert(C124);
  D = clause({~event(x1,x2), accessible_world(x3,x1), event(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C125 = clause({~event(x1,x2), accessible_world(x3,x1), event(x4,x2), accessible_world(x4,x3)});
  wtree.insert(C125);
  D = clause({~event(x1,skc13), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C126 = clause({~event(x1,skc13), accessible_world(skc8,x1)});
  wtree.insert(C126);
  D = clause({event(x1,x2), accessible_world(x1,x3), ~eventuality(x3,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C127 = clause({event(x1,x2), accessible_world(x1,x3), ~eventuality(x3,x2)});
  wtree.insert(C127);
  D = clause({event(x1,x2), accessible_world(x1,x3), ~event(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({~smoke(x1,x2), accessible_world(x3,x1), smoke(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C128 = clause({~smoke(x1,x2), accessible_world(x3,x1), smoke(x4,x2), accessible_world(x4,x3)});
  wtree.insert(C128);
  D = clause({~smoke(x1,skf1(x2)), accessible_world(skc12,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C129 = clause({~smoke(x1,skf1(x2)), accessible_world(skc12,x1)});
  wtree.insert(C129);
  D = clause({smoke(x1,x2), accessible_world(x1,x3), ~event(x3,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C130 = clause({smoke(x1,x2), accessible_world(x1,x3), ~event(x3,x2)});
  wtree.insert(C130);
  D = clause({smoke(x1,x2), accessible_world(x1,x3), ~smoke(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({~state(x1,x2), accessible_world(x3,x1), state(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C131 = clause({~state(x1,x2), accessible_world(x3,x1), state(x4,x2), accessible_world(x4,x3)});
  wtree.insert(C131);
  D = clause({~state(x1,skc9), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C132 = clause({~state(x1,skc9), accessible_world(skc8,x1)});
  wtree.insert(C132);
  D = clause({state(x1,x2), accessible_world(x1,x3), ~event(x3,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C133 = clause({state(x1,x2), accessible_world(x1,x3), ~event(x3,x2)});
  wtree.insert(C133);
  D = clause({state(x1,x2), accessible_world(x1,x3), ~eventuality(x3,x2)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C134 = clause({state(x1,x2), accessible_world(x1,x3), ~eventuality(x3,x2)});
  wtree.insert(C134);
  D = clause({state(x1,x2), accessible_world(x1,x3), ~state(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  D = clause({~proposition(x1,x2), accessible_world(x3,x1), proposition(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C135 = clause({~proposition(x1,x2), accessible_world(x3,x1), proposition(x4,x2), accessible_world(x4,x3)});
  wtree.insert(C135);
  D = clause({~proposition(x1,skc12), accessible_world(skc8,x1)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C136 = clause({~proposition(x1,skc12), accessible_world(skc8,x1)});
  wtree.insert(C136);
  D = clause({proposition(x1,x2), accessible_world(x1,x3), ~proposition(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  wtree.remove(C113);
  D = clause({~event(skc8,skc9)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C137 = clause({~event(skc8,skc9)});
  wtree.insert(C137);
  D = clause({think_believe_consider(x1,x2), accessible_world(x1,x3), ~think_believe_consider(x4,x2), accessible_world(x3,x4)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();
  Kernel::Clause* C138 = clause({think_believe_consider(x1,x2), accessible_world(x1,x3), ~think_believe_consider(x4,x2), accessible_world(x3,x4)});
  wtree.insert(C138);
  D = clause({~think_believe_consider(x1,x2), accessible_world(x3,x1), think_believe_consider(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  m.next(resolvedQueryLit);
  m.reset();

  D = clause({~think_believe_consider(x1,x2), accessible_world(x3,x1), think_believe_consider(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  Kernel::Clause* premise;
  SATSubsumption::SATSubsumptionAndResolution satSubs;

  //std::ofstream out("test.log");
  //out << "Tree is:" << std::endl;
  //out << wtree << std::endl;

  premise = m.next(resolvedQueryLit);
  std::cout << resolvedQueryLit << std::endl;
  ASS_NEQ(resolvedQueryLit, -1);
  ASS(satSubs.checkSubsumptionResolutionWithLiteral(premise, D, resolvedQueryLit));
}

TEST_FUN(reproducerMinimized)
{
  MY_SYNTAX_SUGAR
  ClauseCodeTree<false> wtree;

  ClauseCodeTree<false>::ClauseMatcher m;
  Kernel::Clause* D;
  int resolvedQueryLit;


  Kernel::Clause* C8 = clause({ accessible_world(x1,x2), ~human_person(x2,x3) });
  wtree.insert(C8);
  Kernel::Clause* C50 = clause({ accessible_world(x1,x2), ~be(x2,x3,x4,x5) });
  wtree.insert(C50);
  Kernel::Clause* C52 = clause({ think_believe_consider(x1,x3), ~think_believe_consider(x2,x3), accessible_world(x1,x2) });
  wtree.insert(C52);
  Kernel::Clause* C67 = clause({ accessible_world(x1,x2), proposition(x1,x3) });
  wtree.insert(C67);
  Kernel::Clause* C75 = clause({ ~state(x2,x3), accessible_world(x1,x2) });
  wtree.insert(C75);
  Kernel::Clause* C130 = clause({ smoke(x1,x2), accessible_world(x1,x3) });
  wtree.insert(C130);
  Kernel::Clause* C133 = clause({ accessible_world(x1,x3), ~event(x3,x2) });
  wtree.insert(C133);
  Kernel::Clause* C134 = clause({ accessible_world(x1,x3), ~eventuality(x3,x2) });
  wtree.insert(C134);
  Kernel::Clause* C138 = clause({ think_believe_consider(x1,x2), accessible_world(x1,x3) });
  wtree.insert(C138);

  std::cout << wtree << std::endl;

  D = clause({~think_believe_consider(x1,x2), accessible_world(x3,x1), think_believe_consider(x4,x2), accessible_world(x4,x3)});
  m.init(&wtree, D, true);
  Kernel::Clause* premise;
  SATSubsumption::SATSubsumptionAndResolution satSubs;

  //std::ofstream out("test.log");
  //out << "Tree is:" << std::endl;
  //out << wtree << std::endl;

  premise = m.next(resolvedQueryLit);
  std::cout << resolvedQueryLit << std::endl;
  ASS_NEQ(resolvedQueryLit, -1);
  ASS(satSubs.checkSubsumptionResolutionWithLiteral(premise, D, resolvedQueryLit));
}
}
