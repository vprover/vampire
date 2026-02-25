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
#include "Lib/Stack.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/SATLiteral.hpp"
#include "Test/UnitTesting.hpp"

using namespace SAT;

static SATClause* makeClause(std::initializer_list<SATLiteral> lits)
{
  SATLiteralStack stack;
  for (auto l : lits) {
    stack.push(l);
  }
  return SATClause::fromStack(stack);
}

TEST_FUN(removeDuplicateLiterals_no_duplicates)
{
  // {1, 2, 3} should be returned as-is
  SATClause* cl = makeClause({SATLiteral(1, true), SATLiteral(2, false), SATLiteral(3, true)});
  SATClause* result = SATClause::removeDuplicateLiterals(cl);
  ASS(result != 0);
  ASS_EQ(result->length(), 3u);
}

TEST_FUN(removeDuplicateLiterals_with_duplicates)
{
  // {1, 2, 2, 3} should become {1, 2, 3}
  SATClause* cl = makeClause({SATLiteral(1, false), SATLiteral(2, true), SATLiteral(3, false), SATLiteral(2, true)});
  SATClause* result = SATClause::removeDuplicateLiterals(cl);
  ASS(result != 0);
  ASS_EQ(result->length(), 3u);
  // result is sorted, so we can check order: var 1, var 2, var 3
  ASS_EQ((*result)[0].var(), 1u);
  ASS_EQ((*result)[1].var(), 2u);
  ASS_EQ((*result)[2].var(), 3u);
}

TEST_FUN(removeDuplicateLiterals_triple_duplicate)
{
  // {1, 1, 1} should become {1}
  SATClause* cl = makeClause({SATLiteral(1, true), SATLiteral(1, true), SATLiteral(1, true)});
  SATClause* result = SATClause::removeDuplicateLiterals(cl);
  ASS(result != 0);
  ASS_EQ(result->length(), 1u);
  ASS_EQ((*result)[0].var(), 1u);
  ASS((*result)[0].positive());
}

TEST_FUN(removeDuplicateLiterals_tautology)
{
  // {1, -1} is a tautology, should return 0
  SATClause* cl = makeClause({SATLiteral(1, true), SATLiteral(1, false)});
  SATClause* result = SATClause::removeDuplicateLiterals(cl);
  ASS_EQ(result, static_cast<SATClause*>(0));
}

TEST_FUN(removeDuplicateLiterals_tautology_among_others)
{
  // {2, 1, -1, 3} contains complementary pair on var 1, should return 0
  SATClause* cl = makeClause({SATLiteral(2, true), SATLiteral(1, true), SATLiteral(3, true), SATLiteral(1, false)});
  SATClause* result = SATClause::removeDuplicateLiterals(cl);
  ASS_EQ(result, static_cast<SATClause*>(0));
}
