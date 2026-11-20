/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/ALASCA/Preprocessor.hpp"
#include "Kernel/Problem.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Test/UnitTesting.hpp"

using namespace Kernel;
using namespace Lib;
using namespace Test;

namespace {

template<class Check>
void withConversion(Clause* input, Check check)
{
  Problem problem(new UnitList(input));
  InequalityNormalizer normalizer;
  AlascaPreprocessor(normalizer).integerConversion(problem);
  ASS_EQ(UnitList::length(problem.units()), 1);
  auto actual = static_cast<Clause*>(problem.units()->head());
  check(actual);
  UnitList::destroy(problem.units());
  problem.units() = nullptr;
  if (actual != input) {
    actual->destroy();
  }
  input->decRefCnt();
}

void checkConversion(Clause* input, Clause* expected)
{
  withConversion(input, [&](Clause* actual) {
    ASS_REP2(TestUtils::eqModAC(actual, expected), *actual, *expected);
  });
  expected->destroy();
}

}

TEST_FUN(guard_integer_variable_in_scaled_equality)
{
  NUMBER_SUGAR(Int)
  DECL_VAR_SORTED(x, 0, Int)
  auto input = clause({ 2 * x != 1 });
  auto realX = TermList::var(0);
  auto expected = clause({
    RealTraits::eq(false, realX, RealTraits::floor(realX)),
    RealTraits::eq(false, RealTraits::add(RealTraits::constantTl(-1),
      RealTraits::linMul(RealConstantType(2), realX)), RealTraits::constantTl(0))
  });
  checkConversion(input, expected);
}

TEST_FUN(guard_integer_variables_in_predicates)
{
  NUMBER_SUGAR(Int)
  DECL_VAR_SORTED(x, 0, Int)
  DECL_PRED(p, {Int})
  auto input = clause({ p(x) });
  withConversion(input, [](Clause* actual) {
    ASS_EQ(actual->length(), 2);
    auto realX = TermList::var(0);
    auto guard = RealTraits::eq(false, realX, RealTraits::floor(realX));
    ASS_REP((*actual)[0] == guard || (*actual)[1] == guard, *actual);
  });
}

TEST_FUN(guard_each_integer_variable_once)
{
  NUMBER_SUGAR(Int)
  DECL_VAR_SORTED(x, 0, Int)
  DECL_VAR_SORTED(y, 1, Int)
  DECL_PRED(p, {Int, Int})
  withConversion(clause({ p(x, y), p(y, x) }), [](Clause* actual) {
    ASS_EQ(actual->length(), 4);
    for (unsigned var : {0U, 1U}) {
      auto x = TermList::var(var);
      auto guard = RealTraits::eq(false, x, RealTraits::floor(x));
      unsigned count = 0;
      for (auto lit : actual->iterLits()) {
        count += lit == guard;
      }
      ASS_EQ(count, 1);
    }
  });
}

TEST_FUN(leave_real_variables_unrestricted)
{
  DECL_VAR_SORTED(x, 0, IntTraits::sort())
  DECL_VAR_SORTED(y, 1, RealTraits::sort())
  DECL_PRED(p, {IntTraits::sort(), RealTraits::sort()})
  withConversion(clause({ p(x, y) }), [](Clause* actual) {
    ASS_EQ(actual->length(), 2);
    auto x = TermList::var(0);
    auto guard = RealTraits::eq(false, x, RealTraits::floor(x));
    ASS_REP((*actual)[0] == guard || (*actual)[1] == guard, *actual);
  });
}

TEST_FUN(no_guard_for_ground_arithmetic)
{
  NUMBER_SUGAR(Int)
  checkConversion(clause({ TermSugar(2) != TermSugar(1) }), clause({
    RealTraits::eq(false, RealTraits::constantTl(0), RealTraits::constantTl(1))
  }));
}
