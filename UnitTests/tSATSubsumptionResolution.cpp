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

#include "SATSubsumption/SATSubsumptionAndResolution.hpp"

using namespace std;
using namespace SATSubsumption;
using namespace Test;

#define SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION  \
 __ALLOW_UNUSED(                             \
    DECL_DEFAULT_VARS \
    DECL_VAR(x1, 1) \
    DECL_VAR(x2, 2) \
    DECL_VAR(x3, 3) \
    DECL_VAR(x4, 4) \
    DECL_VAR(x5, 5) \
    DECL_VAR(x6, 6) \
    DECL_VAR(x7, 7) \
    DECL_VAR(y1, 11) \
    DECL_VAR(y2, 12) \
    DECL_VAR(y3, 13) \
    DECL_VAR(y4, 14) \
    DECL_VAR(y5, 15) \
    DECL_VAR(y6, 16) \
    DECL_VAR(y7, 17) \
    DECL_SORT(s) \
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
    DECL_PRED(p, {s}) \
    DECL_PRED(p2, {s, s}) \
    DECL_PRED(p3, {s, s, s}) \
    DECL_PRED(q, {s}) \
    DECL_PRED(q2, {s, s}) \
    DECL_PRED(r, {s}) \
    DECL_PRED(r2, {s, s}) )

template <typename HayStack, typename Needle>
static bool contains(const HayStack& haystack, const Needle& needle)
{
  for (auto candidate : haystack)
    if (candidate == needle)
      return true;
  return false;
}

static void checkConsistency(SATSubsumptionAndResolution::MatchSet& matchSet, std::vector<SATSubsumptionAndResolution::Match>& matches)
{
  ASS_EQ(matchSet.allMatches().size(), matches.size());
  for (auto match : matches) {
    ASS(contains(matchSet.getIMatches(match.i), match));
    ASS(contains(matchSet.getJMatches(match.j), match));
    ASS(matchSet.getMatchForVar(match.var) == match);
    ASS(contains(matchSet.allMatches(), match));
  }
}

static bool checkClauseEquality(Literal const* const lits1[], unsigned len1, Literal const* const lits2[], unsigned len2)
{
  if (len1 != len2) {
    return false;
  }
  // Copy given literals so we can sort them
  std::vector<Literal const*> c1(lits1, lits1 + len1);
  std::vector<Literal const*> c2(lits2, lits2 + len2);
  // The equality tests only make sense for shared literals
  std::for_each(c1.begin(), c1.end(), [](Literal const* lit) { ASS(lit->shared()); });
  std::for_each(c2.begin(), c2.end(), [](Literal const* lit) { ASS(lit->shared()); });
  // Sort input by pointer value
  // NOTE: we use std::less<> because the C++ standard guarantees it is a total order on pointer types.
  //       (the built-in operator< is not required to be a total order for pointer types.)
  std::less<Literal const*> const lit_ptr_less{};
  std::sort(c1.begin(), c1.end(), lit_ptr_less);
  std::sort(c2.begin(), c2.end(), lit_ptr_less);
  // Finally check the equality
  return c1 == c2;
}

static bool checkClauseEquality(Clause* const cl1, Clause* const cl2)
{
  return checkClauseEquality(cl1->literals(), cl1->length(), cl2->literals(), cl2->length());
}

TEST_FUN(MatchSetIndexing)
{
  SATSubsumptionAndResolution::MatchSet matchSet;
  matchSet.resize(3, 3);

  std::vector<SATSubsumptionAndResolution::Match> matches;
  SATSubsumptionAndResolution::Match match1 = matchSet.addMatch(0, 0, true, subsat::Var(0));
  SATSubsumptionAndResolution::Match match2 = matchSet.addMatch(2, 1, true, subsat::Var(1));
  SATSubsumptionAndResolution::Match match3 = matchSet.addMatch(2, 2, true, subsat::Var(2));
  matchSet.indexMatrix();

  ASS(match1 != match2);
  ASS(match2 != match3);
  ASS(match3 != match1);

  matches.push_back(match1);
  matches.push_back(match2);
  matches.push_back(match3);

  // Check that the matches are in the correct indices
  checkConsistency(matchSet, matches);
}

TEST_FUN(Allocation)
{
  SATSubsumptionAndResolution* subsumption = new SATSubsumptionAndResolution();
  ASS(subsumption);
  delete subsumption;
}

TEST_FUN(PositiveSubsumption)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    SATSubsumptionAndResolution subsumption;

  std::vector<Kernel::Clause*> L;
  std::vector<Kernel::Clause*> M;

  // Test 1
  L.push_back(clause({ p3(x1, x2, x3), p3(f(x2), x4, x4) }));
  M.push_back(clause({ p3(f(c), d, y1), p3(f(d), c, c) }));

  // Test 2
  L.push_back(clause({ p3(x1, x2, x3), p3(f(x2), x4, x4) }));
  M.push_back(clause({ p3(f(c), d, y1), p3(f(d), c, c), r(x1) }));

  // Test 3
  L.push_back(clause({ p(f2(f(g(x1)), x1)), c == g(x1) }));
  M.push_back(clause({ g(y1) == c, p(f2(f(g(y1)), y1)) }));

  // Test 4
  L.push_back(clause({ f2(x1, x2) == c, ~p2(x1, x3), p2(f(f2(x1, x2)), f(x3)) }));
  M.push_back(clause({ c == f2(x3, y2), ~p2(x3, y1), p2(f(f2(x3, y2)), f(y1)) }));

  // Test 5
  L.push_back(clause({ p(f2(f(e), g2(x4, x3))), p2(f2(f(e), g2(x4, x3)), x3), f(e) == g2(x4, x3) }));
  M.push_back(clause({ p(f2(f(e), g2(y1, y3))), p2(f2(f(e), g2(y1, y3)), y3), f(e) == g2(y1, y3) }));

  // Test 6
  L.push_back(clause({ p3(y7, f(y1), x4), ~p3(y7, y1, x4) }));
  M.push_back(clause({ p3(x6, f(y3), d), ~p3(x6, y3, d) }));

  // // Test 7
  // L.push_back(clause({~p(x1), p(f(x1))}));
  // M.push_back(clause({~p(x1), p(f(f(x1)))}));

  bool success = true;
  for (unsigned i = 0; i < L.size(); i++) {
    if (!subsumption.checkSubsumption(L[i], M[i])) {
      std::cerr << "Test " << i + 1 << " failed" << std::endl;
      success = false;
    }
  }

  ASS(success)
}

TEST_FUN(NegativeSubsumption)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    SATSubsumptionAndResolution subsumption;

  std::vector<Kernel::Clause*> L;
  std::vector<Kernel::Clause*> M;

  // Test 1
  L.push_back(clause({ p2(f2(g2(x1, x2), x3), x3), p2(f2(g2(x1, x2), x3), x2), g2(x1, x2) == x3 }));
  M.push_back(clause({ p2(f2(g2(y1, y2), y2), y2), g2(y1, y2) == y2, ~p2(f2(g2(y1, y2), y2), g2(y1, y2)) }));

  // Test 2
  L.push_back(clause({ ~p2(x1, x2), p(x1) }));
  M.push_back(clause({ p(y1), ~p(f(f2(f2(y2, y2), f2(y2, y3)))), ~p(y3), ~p(y2) }));

  // Test 3
  L.push_back(clause({ p2(y5, f(f2(c, x1))), ~p(c), ~p(y5) }));
  M.push_back(clause({ ~q(f(d)), p2(c, f(f2(c, x4))), r(e), ~p(c), d == g(c) }));

  // Test 4
  L.push_back(clause({ p2(y5, f(f2(x1, c))), ~p(c), ~p(y5) }));
  M.push_back(clause({ ~q(d), p2(c, f(f2(x4, c))), r(d), ~p(c), d == g(c) }));

  // Test 5
  L.push_back(clause({ p(x1), x1 == f(x2), p(x2) }));
  M.push_back(clause({ p(y1), y1 == f(y1) }));

  // Test 6
  L.push_back(clause({ p(x1), x1 == f(x2), p(x2), q(x1) }));
  M.push_back(clause({ p(y1), y1 == f(y1), q(y2), r(y3) }));

  // Test 7
  L.push_back(clause({ p(f(x1)), p(f(x2)) }));
  M.push_back(clause({ p(f(y1)), p(g(y2)) }));

  bool success = true;
  for (unsigned i = 0; i < L.size(); i++) {
    if (subsumption.checkSubsumption(L[i], M[i])) {
      std::cerr << "Test " << i + 1 << " failed" << std::endl;
      success = false;
    }
  }

  ASS(success)
}

/**
 * Check that the subsumption resolution works for positive instances
 */
TEST_FUN(PositiveSubsumptionResolution)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    Kernel::Clause* conclusion;
  SATSubsumptionAndResolution subsumption;

  std::vector<Kernel::Clause*> L;
  std::vector<Kernel::Clause*> M;
  std::vector<Kernel::Clause*> expected;

  // Test 1
  L.push_back(clause({ ~p(x1), q(x1) }));
  M.push_back(clause({ p(c), q(c), r(e) }));
  expected.push_back(clause({ q(c), r(e) }));

  // Test 2
  L.push_back(clause({ p2(x1, x2), p2(f(x2), x3) }));
  M.push_back(clause({ ~p2(f(y1), d), p2(g(y1), c), ~p2(f(c), e) }));
  expected.push_back(clause({ ~p2(f(y1), d), p2(g(y1), c) }));

  // Test 3
  L.push_back(clause({ p3(x2, f(x2), e) }));
  M.push_back(clause({ p3(f(e), x5, x5), ~p3(x4, f(x4), e) }));
  expected.push_back(clause({ p3(f(e), x5, x5) }));

  // Test 4
  L.push_back(clause({ p(c) }));
  M.push_back(clause({ ~p(c) }));
  expected.push_back(clause({}));

  // Test 5
  L.push_back(clause({ ~p(f(x1)), q(x1) }));
  M.push_back(clause({ ~p2(x2, x5), q(x2), p(f(x2)), ~q(g(x5)) }));
  expected.push_back(clause({ ~p2(x2, x5), q(x2), ~q(g(x5)) }));

  // Test 6
  L.push_back(clause({ p(f2(y7, x6)), p2(y7, x6) }));
  M.push_back(clause({ p2(f(g(x5)), y4), ~p(f2(f(g(x5)), y4)), ~p2(f2(f(g(x5)), y4), x5) }));
  expected.push_back(nullptr);

  // Test 7
  L.push_back(clause({ p(f2(y7, x6)), p2(y7, x6) }));
  M.push_back(clause({ p2(f(g(x5)), y4), ~p(f2(f(g(x5)), y4)), ~p2(f2(f(g(x5)), y4), x5) }));
  expected.push_back(nullptr);

  // Test 8
  L.push_back(clause({ ~p2(y7, d) }));
  M.push_back(clause({ ~p(x6), ~p(x5), ~p2(f(f2(f2(x5, x5), f2(x5, x6))), x6), p2(f2(f2(x5, x5), f2(x5, x6)), d) }));
  expected.push_back(nullptr);

  // Test 9
  L.push_back(clause({ ~p3(d, y7, d), ~p3(y7, e, c) }));
  M.push_back(clause({ p3(d, x6, d), ~p3(x6, e, c) }));
  expected.push_back(nullptr);

  // Test 10
  L.push_back(clause({ p2(y7, x6), f2(y7, x6) == f2(f3(x5, y4, x4), x4), p2(y4, x4) }));
  M.push_back(clause({ ~p2(g2(h2(y3, x2), x2), x7), f2(g2(h2(y3, x2), x2), x7) == f2(f3(y6, g2(h2(y3, x2), x2), x7), x7) }));
  expected.push_back(nullptr);

  // Test 11
  L.push_back(clause({ p2(y7, x6), ~q2(x5, x6), ~p2(y7, x5) }));
  M.push_back(clause({ p2(f2(y4, x6), y4), ~p2(x6, y7), ~r2(y4, y7), ~p2(x6, d), ~q2(y4, d), ~q2(y7, d) }));
  expected.push_back(nullptr);

  // Test 12
  L.push_back(clause({ p(d) }));
  M.push_back(clause({ q(d), ~p(d) }));
  expected.push_back(nullptr);

  bool success = true;

  for (unsigned i = 0; i < L.size(); i++) {
    conclusion = subsumption.checkSubsumptionResolution(L[i], M[i], false, false);
    if (conclusion == nullptr) {
      std::cerr << "Test " << i + 1 << " failed: no conclusion generated" << std::endl;
      success = false;
    }
    if (expected[i] != nullptr && conclusion != nullptr) {
      if (!checkClauseEquality(conclusion, expected[i])) {
        std::cerr << "Test " << i << " failed: wrong conclusion" << std::endl;
        std::cerr << "Expected: " << expected[i]->toString() << std::endl;
        std::cerr << "Actual: " << conclusion->toString() << std::endl;
        success = false;
      }
    }
  }

  ASS(success)
}

TEST_FUN(NegativeSubsumptionResolution)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION)
    Kernel::Clause* conclusion;
  SATSubsumptionAndResolution subsumption;

  std::vector<Kernel::Clause*> L;
  std::vector<Kernel::Clause*> M;

  // Test 1
  L.push_back(clause({ ~p(x1), q(x1) }));
  M.push_back(clause({ p(c), q(d), r(e) }));

  // Test 2
  L.push_back(clause({ ~p(x1), ~q(x2) }));
  M.push_back(clause({ p(c), q(d), r(e) }));

  // Test 3
  L.push_back(clause({ ~p(x1), r(c) }));
  M.push_back(clause({ p(c), q(d), r(e) }));

  // Test 4
  L.push_back(clause({ ~p(x1), p2(x1, x2) }));
  M.push_back(clause({ p(c), q(d), r(e) }));

  // Test 5
  L.push_back(clause({ p3(x1, x2, x2), ~p3(x2, c, c) }));
  M.push_back(clause({ p3(y1, c, c), ~p3(y1, y2, y2) }));

  // Test 6
  L.push_back(clause({ p3(y7, x6, x6), ~p3(y7, d, d) }));
  M.push_back(clause({ p3(x5, d, d), ~p3(x5, x6, x6) }));

  // Test 7
  L.push_back(clause({ ~p3(y7, d, d), p3(y7, x6, x6) }));
  M.push_back(clause({ ~p3(x5, y4, f(f2(x4, f(y3)))), p3(x2, d, d), ~p3(x7, x4, y3), ~p3(x2, f2(x5, y4), x7) }));

  // Test 8
  L.push_back(clause({ ~p3(y7, d, d), p3(y7, x6, x6) }));
  M.push_back(clause({ ~p3(x5, x6, x6), p3(d, d, x5) }));

  // Test 9
  L.push_back(clause({ ~p3(d, y7, d), p3(x6, y7, x6) }));
  M.push_back(clause({ p3(d, x5, d), ~p3(y4, f(y4), f(x5)) }));

  // Test 10
  L.push_back(clause({ ~p3(d, d, d), p3(f(f(y7)), d, y7) }));
  M.push_back(clause({ p3(d, x6, x6) }));

  // Test 11
  L.push_back(clause({ p2(y7, d), p2(e, y7), e == y7 }));
  M.push_back(clause({ ~p2(x6, x5), ~p2(y7, x6), p2(y7, x5) }));

  // Test 12
  L.push_back(clause({ f2(y1, y3) == x1, ~p2(g2(x1, f2(y1, y3)), x1), ~p2(g2(x1, f2(y1, y3)), y1), ~p2(g2(x1, f2(y1, y3)), y3) }));
  M.push_back(clause({ p2(g2(x2, f2(y1, y3)), x2), f2(y1, y3) == x2, p2(g2(x2, f2(y1, y3)), y3) }));

  bool success = true;

  for (unsigned i = 0; i < L.size(); i++) {
    conclusion = subsumption.checkSubsumptionResolution(L[i], M[i], false, false);
    if (conclusion != nullptr) {
      std::cerr << "Test " << i + 1 << " failed: conclusion generated" << std::endl;
      std::cerr << "Conclusion: " << conclusion->toString() << std::endl;
      success = false;
    }
  }

  ASS(success)
}

TEST_FUN(UsePreviousSettings)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION);
  SATSubsumptionAndResolution subsumption;
  Kernel::Clause* conclusion = nullptr;

  // subsumption works but not SR
  Kernel::Clause* L1 = clause({ p(x1), q(x2) });
  Kernel::Clause* M1 = clause({ p(c), q(y1) });
  ASS(subsumption.checkSubsumption(L1, M1, true));
  conclusion = subsumption.checkSubsumptionResolution(L1, M1, false, true);
  ASS(!conclusion);

  // subsumption and SR don't work
  Kernel::Clause* L2 = clause({ p(x1), r(x2) });
  Kernel::Clause* M2 = clause({ p(c), q(y1) });
  ASS(!subsumption.checkSubsumption(L2, M2, true));
  conclusion = subsumption.checkSubsumptionResolution(L2, M2, false, true);
  ASS(!conclusion);

  // SR works but not subsumption
  Kernel::Clause* L3 = clause({ p(x1), q(x2) });
  Kernel::Clause* M3 = clause({ p(y1), ~q(c) });
  Kernel::Clause* expected3 = clause({ p(y1) });
  ASS(!subsumption.checkSubsumption(L3, M3, true));
  conclusion = subsumption.checkSubsumptionResolution(L3, M3, false, true);
  ASS(conclusion);
  ASS(checkClauseEquality(conclusion, expected3));

  Kernel::Clause* L4 = clause({ p2(y3, y5), ~q2(x7, y5), ~p2(y3, x7) });
  Kernel::Clause* M4 = clause({ p2(f2(y2, y5), y2), ~p2(y5, y3), ~r2(y2, y3), ~p2(y5, c), ~q2(y2, c), ~q2(y3, c) });
  ASS(!subsumption.checkSubsumption(L4, M4, true));
  conclusion = subsumption.checkSubsumptionResolution(L4, M4, false, true);
  ASS(conclusion);

  Kernel::Clause* L5 = clause({ p3(y1, y5, x7), ~p3(x2, x3, x7), ~p3(y3, y5, x3), ~p3(x2, y3, y1) });
  Kernel::Clause* M5 = clause({ p3(x1, x6, y4), ~p3(y2, x4, y4), ~p3(y6, x4, x6), ~p3(x1, y6, y2) });
  ASS(!subsumption.checkSubsumption(L5, M5, true));
  conclusion = subsumption.checkSubsumptionResolution(L5, M5, false, true);
  ASS(!conclusion);
}

TEST_FUN(PaperExample)
{
  __ALLOW_UNUSED(SYNTAX_SUGAR_SUBSUMPTION_RESOLUTION);
  Kernel::Clause* conclusion;
  SATSubsumptionAndResolution subsumption;

  std::vector<Kernel::Clause*> L;
  std::vector<Kernel::Clause*> M;
  std::vector<Kernel::Clause*> expected;

  // Test 1
  L.push_back(clause({ p2(f(x1), x2), ~p2(x2, x1), p2(f(x3), x1) }));
  M.push_back(clause({ ~p2(f(c), d), ~p2(d, c), p2(f(y1), c) }));
  expected.push_back(clause({ ~p2(d, c), p2(f(y1), c) }));

  bool success = true;

  for (unsigned i = 0; i < L.size(); i++) {
    conclusion = subsumption.checkSubsumptionResolution(L[i], M[i], false, false);
    if (conclusion == nullptr) {
      std::cerr << "Test " << i + 1 << " failed: no conclusion generated" << std::endl;
      success = false;
    }
    if (expected[i] != nullptr && conclusion != nullptr) {
      if (!checkClauseEquality(conclusion, expected[i])) {
        std::cerr << "Test " << i << " failed: wrong conclusion" << std::endl;
        std::cerr << "Expected: " << expected[i]->toString() << std::endl;
        std::cerr << "Actual: " << conclusion->toString() << std::endl;
        success = false;
      }
    }
  }

  ASS(success)
}
