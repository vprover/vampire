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

#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "SATSubsumption/Util.hpp"
#include "Kernel/Inference.hpp"

using namespace std;
using namespace SATSubsumption;
using namespace Test;

#define SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION     \
  __ALLOW_UNUSED(                               \
  DECL_DEFAULT_VARS                             \
  DECL_VAR(x1, 1)                               \
  DECL_VAR(x2, 2)                               \
  DECL_VAR(x3, 3)                               \
  DECL_VAR(x4, 4)                               \
  DECL_VAR(x5, 5)                               \
  DECL_VAR(x6, 6)                               \
  DECL_VAR(x7, 7)                               \
  DECL_VAR(y1, 11)                              \
  DECL_VAR(y2, 12)                              \
  DECL_VAR(y3, 13)                              \
  DECL_VAR(y4, 14)                              \
  DECL_VAR(y5, 15)                              \
  DECL_VAR(y6, 16)                              \
  DECL_VAR(y7, 17)                              \
  DECL_SORT(s)                                  \
  DECL_CONST(c, s)                              \
  DECL_CONST(d, s)                              \
  DECL_CONST(e, s)                              \
  DECL_FUNC(f, {s}, s)                          \
  DECL_FUNC(f2, {s, s}, s)                      \
  DECL_FUNC(f3, {s, s, s}, s)                   \
  DECL_FUNC(g, {s}, s)                          \
  DECL_FUNC(g2, {s, s}, s)                      \
  DECL_FUNC(h, {s}, s)                          \
  DECL_FUNC(h2, {s, s}, s)                      \
  DECL_FUNC(i, {s}, s)                          \
  DECL_FUNC(i2, {s, s}, s)                      \
  DECL_PRED(p, {s})                             \
  DECL_PRED(p2, {s, s})                         \
  DECL_PRED(p3, {s, s, s})                      \
  DECL_PRED(q, {s})                             \
  DECL_PRED(q2, {s, s})                         \
  DECL_PRED(r, {s}))

static bool vectorContains(vvector<SATSubsumptionAndResolution::Match> vec, SATSubsumptionAndResolution::Match match)
{
  for (auto m : vec) {
    if (m == match) {
      return true;
    }
  }
  return false;
}

static void checkConsistency(SATSubsumptionAndResolution::MatchSet *matchSet, vvector<SATSubsumptionAndResolution::Match> matches)
{
  ASS_EQ(matchSet->getAllMatches().size(), matches.size());
  for (auto match : matches) {
    ASS(vectorContains(matchSet->getIMatches(match._i), match));
    ASS(vectorContains(matchSet->getJMatches(match._j), match));
    ASS(matchSet->getMatchForVar(match._var) == match);
    ASS(vectorContains(matchSet->getAllMatches(), match));
  }
}

TEST_FUN(MatchSetIndexing)
{
  SATSubsumptionAndResolution::MatchSet *matchSet = new SATSubsumptionAndResolution::MatchSet(3, 3);
  vvector<SATSubsumptionAndResolution::Match> matches;
  SATSubsumptionAndResolution::Match match1 = matchSet->addMatch(0, 0, true, subsat::Var(0));
  SATSubsumptionAndResolution::Match match2 = matchSet->addMatch(2, 1, true, subsat::Var(1));
  SATSubsumptionAndResolution::Match match3 = matchSet->addMatch(2, 2, true, subsat::Var(2));

  ASS(match1 != match2);
  ASS(match2 != match3);
  ASS(match3 != match1);

  matches.push_back(match1);
  matches.push_back(match2);
  matches.push_back(match3);

  // Check that the matches are in the correct indices
  checkConsistency(matchSet, matches);
  matches.clear();
  delete matchSet;
}

TEST_FUN(Allocation)
{
  SATSubsumptionAndResolution *subsumption = new SATSubsumptionAndResolution();
  ASS(subsumption);
  delete subsumption;
}

TEST_FUN(PositiveSubsumption)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
  SATSubsumptionAndResolution subsumption;
  Kernel::Clause *L1 = clause({p3(x1, x2, x3), p3(f(x2), x4, x4)});
  Kernel::Clause *M1 = clause({p3(f(c), d, y1), p3(f(d), c, c)});
  ASS(subsumption.checkSubsumption(L1, M1));

  Kernel::Clause *M2 = clause({p3(f(c), d, y1), p3(f(d), c, c), r(x1)});
  ASS(subsumption.checkSubsumption(L1, M2));

  Kernel::Clause *L3 = clause({p(f2(f(g(x1)), x1)), c == g(x1)});
  Kernel::Clause *M3 = clause({g(y1) == c, p(f2(f(g(y1)), y1))});
  ASS(subsumption.checkSubsumption(L3, M3));

  Kernel::Clause *L4 = clause({f2(x1, x2) == c, ~p2(x1, x3), p2(f(f2(x1, x2)), f(x3))});
  Kernel::Clause *M4 = clause({c == f2(x3, y2), ~p2(x3, y1), p2(f(f2(x3, y2)), f(y1))});
  ASS(subsumption.checkSubsumption(L4, M4));

  Kernel::Clause *L5 = clause({p(f2(f(e), g2(x4, x3))), p2(f2(f(e), g2(x4, x3)), x3), f(e) == g2(x4, x3)});
  Kernel::Clause *M5 = clause({p(f2(f(e), g2(y1, y3))), p2(f2(f(e), g2(y1, y3)), y3), f(e) == g2(y1, y3)});
  ASS(subsumption.checkSubsumption(L5, M5));

  Kernel::Clause* L6 = clause({p3(y7, f(y1), x4), ~p3(y7, y1, x4)});
  Kernel::Clause* M6 = clause({p3(x6, f(y3), d), ~p3(x6, y3, d)});
  ASS(subsumption.checkSubsumption(L6, M6));

}

TEST_FUN(NegativeSubsumption)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
  SATSubsumptionAndResolution subsumption;

  Kernel::Clause *L1 = clause({p2(f2(g2(x1, x2), x3), x3), p2(f2(g2(x1, x2), x3), x2), g2(x1, x2) == x3});
  Kernel::Clause *M1 = clause({p2(f2(g2(y1, y2), y2), y2), g2(y1, y2) == y2, ~p2(f2(g2(y1, y2), y2), g2(y1, y2))});
  ASS(!subsumption.checkSubsumption(L1, M1));

  Kernel::Clause *L2 = clause({~p2(x1, x2), p(x1)});
  Kernel::Clause *M2 = clause({p(y1), ~p(f(f2(f2(y2, y2), f2(y2, y3)))), ~p(y3), ~p(y2)});
  ASS(!subsumption.checkSubsumption(L2, M2));

  Kernel::Clause *L3 = clause({p2(y5, f(f2(c, x1))), ~p(c), ~p(y5)});
  Kernel::Clause *M3 = clause({~q(f(d)), p2(c, f(f2(c, x4))), r(e), ~p(c), d == g(c)});
  ASS(!subsumption.checkSubsumption(L3, M3));

  Kernel::Clause *L4 = clause({p2(y5, f(f2(x1, c))), ~p(c), ~p(y5)});
  Kernel::Clause *M4 = clause({~q(d), p2(c, f(f2(x4, c))), r(d), ~p(c), d == g(c)});
  ASS(!subsumption.checkSubsumption(L4, M4));
}

/**
 * Check that the subsumption resolution works for positive instances
 */
TEST_FUN(PositiveSubsumptionResolution)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
  Kernel::Clause *conclusion;
  SATSubsumptionAndResolution subsumption;

  Kernel::Clause *L1 = clause({~p(x1), q(x1)});
  Kernel::Clause *M1 = clause({p(c), q(c), r(e)});
  Kernel::Clause *expected1 = clause({q(c), r(e)});
  conclusion = subsumption.checkSubsumptionResolution(L1, M1);
  ASS(conclusion)
  ASS(checkClauseEquality(conclusion, expected1));

  Kernel::Clause *L2 = clause({p2(x1, x2), p2(f(x2), x3)});
  Kernel::Clause *M2 = clause({~p2(f(y1), d), p2(g(y1), c), ~p2(f(c), e)});
  Kernel::Clause *expected2 = clause({~p2(f(y1), d), p2(g(y1), c)});
  conclusion = subsumption.checkSubsumptionResolution(L2, M2);
  ASS(conclusion)
  ASS(checkClauseEquality(conclusion, expected2));

  Kernel::Clause *L3 = clause({p3(x2, f(x2), e)});
  Kernel::Clause *M3 = clause({p3(f(e), x5, x5), ~p3(x4, f(x4), e)});
  Kernel::Clause *expected3 = clause({p3(f(e), x5, x5)});
  conclusion = subsumption.checkSubsumptionResolution(L3, M3);
  ASS(conclusion);
  ASS(checkClauseEquality(conclusion, expected3));

  Kernel::Clause *L4 = clause({p(c)});
  Kernel::Clause *M4 = clause({~p(c)});
  Kernel::Clause *expected4 = clause({});
  conclusion = subsumption.checkSubsumptionResolution(L4, M4);
  ASS(conclusion);
  ASS(checkClauseEquality(conclusion, expected4));

  Kernel::Clause* L5 = clause({~p(f(x1)), q(x1)});
  Kernel::Clause* M5 = clause({~p2(x2, x5), q(x2), p(f(x2)), ~q(g(x5))});
  Kernel::Clause* expected5 = clause({~p2(x2, x5), q(x2), ~q(g(x5))});
  conclusion = subsumption.checkSubsumptionResolution(L5, M5);
  ASS(conclusion);
  ASS(checkClauseEquality(conclusion, expected5));

  Kernel::Clause* L6 = clause({p(f2(x1, x2)), p2(x1, x2)});
  Kernel::Clause* M6 = clause({p2(f(g(x5)), y4), ~p(f2(f(g(x5)), y4)), ~p2(f2(f(g(x5)), y4), x5)});
  conclusion = subsumption.checkSubsumptionResolution(L6, M6);
  ASS(conclusion);

  Kernel::Clause* L7 = clause({p(f2(x1, x2)),
                               p2(x1, x2)});
  Kernel::Clause* M7 = clause({p2(f(g(x5)), y4),
                               ~p(f2(f(g(x5)), y4)),
                               ~p2(f2(f(g(x5)), y4), x5)});
  conclusion = subsumption.checkSubsumptionResolution(L7, M7);
  ASS(conclusion);

  Kernel::Clause* L8 = clause({~p2(x6, d)});
  Kernel::Clause* M8 = clause({~p(y1), ~p(x3), ~p2(f(f2(f2(x3, x3), f2(x3, y1))), y1), p2(f2(f2(x3, x3), f2(x3, y1)), d)});
  conclusion = subsumption.checkSubsumptionResolution(L8, M8);
  ASS(conclusion);
  }

  TEST_FUN(NegativeSubsumptionResolution)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
  // Create the the L clause
  Kernel::Clause *L1 = clause({~p(x1), q(x1)});
  Kernel::Clause *L2 = clause({~p(x1), ~q(x2)});
  Kernel::Clause *L3 = clause({~p(x1), r(c)});
  Kernel::Clause *L4 = clause({~p(x1), p2(x1, x2)});
  // Create the M clause
  Kernel::Clause *M1 = clause({p(c), q(d), r(e)});
  // checks
  ASS(L1);
  ASS(M1);

  SATSubsumptionAndResolution subsumption;
  Kernel::Clause *conclusion = subsumption.checkSubsumptionResolution(L1, M1);
  ASS(!conclusion)
  conclusion = subsumption.checkSubsumptionResolution(L2, M1);
  ASS(!conclusion)
  conclusion = subsumption.checkSubsumptionResolution(L3, M1);
  ASS(!conclusion)
  conclusion = subsumption.checkSubsumptionResolution(L4, M1);
  ASS(!conclusion)

  Kernel::Clause *L5 = clause({p3(x1, x2, x2), ~p3(x2, c, c)});
  Kernel::Clause *M5 = clause({p3(y1, c, c), ~p3(y1, y2, y2)});
  conclusion = subsumption.checkSubsumptionResolution(L5, M5);
  if (conclusion) {
    cout << " --- " << conclusion->toString() << endl;
  }
  ASS(!subsumption.checkSubsumptionResolution(L5, M5));

  Kernel::Clause *L6 = clause({p3(x5, x1, x1), ~p3(x5, e, e)});
  Kernel::Clause *M6 = clause({p3(x4, e, e), ~p3(x4, x1, x1)});
  conclusion = subsumption.checkSubsumptionResolution(L6, M6);
  if (conclusion) {
    cout << conclusion->toString() << endl;
  }
  ASS(!conclusion);
  Kernel::Clause *L7 = clause({~p3(x5, e, e), p3(x5, x1, x1)});
  Kernel::Clause *M7 = clause({~p3(x4, x3, f(f2(y4, f(x2)))), p3(y2, e, e), ~p3(y1, y4, x2), ~p3(y2, f2(x4, x3), y1)});
  conclusion = subsumption.checkSubsumptionResolution(L7, M7);
  if (conclusion) {
    cout << conclusion->toString() << endl;
  }
  ASS(!conclusion);
  Kernel::Clause *L8 = clause({~p3(x5, e, e), p3(x5, x1, x1)});
  Kernel::Clause *M8 = clause({~p3(x4, x1, x1), p3(e, e, x4)});
  conclusion = subsumption.checkSubsumptionResolution(L8, M8);
  if (conclusion) {
    cout << conclusion->toString() << endl;
  }
  ASS(!conclusion);
  Kernel::Clause *L9 = clause({~p3(e, x5, e), p3(x1, x5, x1)});
  Kernel::Clause *M9 = clause({p3(e, x4, e), ~p3(x3, f(x3), f(x4))});
  conclusion = subsumption.checkSubsumptionResolution(L9, M9);
  if (conclusion) {
    cout << conclusion->toString() << endl;
  }
  ASS(!conclusion);
  Kernel::Clause *L10 = clause({~p3(e, e, e), p3(f(f(x5)), e, x5)});
  Kernel::Clause *M10 = clause({p3(e, x1, x1)});
  conclusion = subsumption.checkSubsumptionResolution(L10, M10);
  if (conclusion) {
    cout << conclusion->toString() << endl;
  }
  ASS(!conclusion);

  Kernel::Clause* L11 = clause({~p3(d, y7, d), ~p3(y7, c, e)});
  Kernel::Clause* M11 = clause({p3(d, y1, d), ~p3(y1, c, e)});
  conclusion = subsumption.checkSubsumptionResolution(L11, M11);
  ASS(conclusion);

  Kernel::Clause* L13 = clause({p2(x5, x7),
                                f2(x5, x7)==f2(f3(y4, y5, x2), x2),
                                p2(y5, x2)});
  Kernel::Clause* M13 = clause({~p2(y1, x3),
                                f2(y1, x3)==f2(f3(y6, y1, x3), x3)});
  conclusion = subsumption.checkSubsumptionResolution(L13, M13);
  ASS(conclusion);

  Kernel::Clause* L12 = clause({p2(x5, x7),
                                f2(x5, x7)==f2(f3(y4, y5, x2), x2),
                                p2(y5, x2)});
  Kernel::Clause* M12 = clause({~p2(g2(h2(x1, y1), y1), x3),
                                f2(g2(h2(x1, y1), y1), x3)==f2(f3(y6, g2(h2(x1, y1), y1), x3), x3)});
  conclusion = subsumption.checkSubsumptionResolution(L12, M12);

  ASS(conclusion);
}

TEST_FUN(UsePreviousSettings)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
  SATSubsumptionAndResolution subsumption;
  Kernel::Clause *conclusion = nullptr;

  // subsumption works but not SR
  Kernel::Clause *L1 = clause({p(x1), q(x2)});
  Kernel::Clause *M1 = clause({p(c), q(y1)});
  ASS(subsumption.checkSubsumption(L1, M1, true));
  conclusion = subsumption.checkSubsumptionResolution(L1, M1, true);
  ASS(!conclusion);

  // subsumption and SR don't work
  Kernel::Clause *L2 = clause({p(x1), r(x2)});
  Kernel::Clause *M2 = clause({p(c), q(y1)});
  ASS(!subsumption.checkSubsumption(L2, M2, true));
  conclusion = subsumption.checkSubsumptionResolution(L2, M2, true);
  ASS(!conclusion);

  // SR works but not subsumption
  Kernel::Clause *L3 = clause({p(x1), q(x2)});
  Kernel::Clause *M3 = clause({p(y1), ~q(c)});
  Kernel::Clause *expected3 = clause({p(y1)});
  ASS(!subsumption.checkSubsumption(L3, M3, true));
  conclusion = subsumption.checkSubsumptionResolution(L3, M3, true);
  ASS(conclusion);
  ASS(checkClauseEquality(conclusion, expected3));
}
