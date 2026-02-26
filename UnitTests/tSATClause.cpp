/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Debug/Assertion.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"
#include "Test/UnitTesting.hpp"

using namespace SAT;

#define p SATLiteral(1, true)
#define q SATLiteral(2, true)
#define r SATLiteral(3, true)

SATLiteral operator~(const SATLiteral& lit) {
  return lit.opposite();
}

static SATClause* satClause(SATLiteralStack lits)
{
  return SATClause::fromStack(lits);
}

TEST_FUN(removeDuplicateLiterals_no_duplicates)
{
  // {p, ~q, r} should be returned as-is
  auto cl = satClause({ p, ~q, r });
  auto result = SATClause::removeDuplicateLiterals(cl);

  ASS(result);
  ASS_EQ(result->length(), 3u);
}

TEST_FUN(removeDuplicateLiterals_with_duplicates)
{
  // {~p, q, q, ~r} should become {~p, q, ~r}
  auto cl = satClause({ ~p, q, ~r, q });
  auto result = SATClause::removeDuplicateLiterals(cl);

  ASS(result);
  ASS_EQ(result->length(), 3u);
  // result is sorted, so we can check order: var 1, var 2, var 3
  ASS_EQ((*result)[0].var(), 1u);
  ASS_EQ((*result)[1].var(), 2u);
  ASS_EQ((*result)[2].var(), 3u);
}

TEST_FUN(removeDuplicateLiterals_triple_duplicate)
{
  // {p, p, p} should become {p}
  auto cl = satClause({ p, p, p });
  auto result = SATClause::removeDuplicateLiterals(cl);

  ASS(result);
  ASS_EQ(result->length(), 1u);
  ASS_EQ((*result)[0].var(), 1u);
  ASS((*result)[0].positive());
}

TEST_FUN(removeDuplicateLiterals_tautology)
{
  // {p, ~p} is a tautology, should return 0
  auto cl = satClause({ p, ~p });
  auto result = SATClause::removeDuplicateLiterals(cl);

  ASS(!result);
}

TEST_FUN(removeDuplicateLiterals_tautology_among_others)
{
  // {p, ~p, q, r} contains complementary pair p and ~p, should return 0
  auto cl = satClause({ q, p, r, ~p });
  auto result = SATClause::removeDuplicateLiterals(cl);

  ASS(!result);
}
