/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "DP/SimpleCongruenceClosure.hpp"
#include "Kernel/LPO.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Test/UnitTesting.hpp"

#include <memory>

using namespace DP;
using namespace Kernel;
using namespace Lib;

namespace {

LPO ordering(bool reverse = false)
{
  auto functions = DArray<int>::fromIterator(getRangeIterator(0, (int)env.signature->functions()));
  if (reverse) {
    for (unsigned i = 0; i < functions.size(); ++i) {
      functions[i] = functions.size() - 1 - i;
    }
  }
  return LPO(std::move(functions),
      DArray<int>::fromIterator(getRangeIterator(0, (int)env.signature->typeCons())),
      DArray<int>::fromIterator(getRangeIterator(0, (int)env.signature->predicates())),
      PrecedenceOrdering::testLevels(), false);
}

void checkModel(SimpleCongruenceClosure& cc, std::initializer_list<Literal*> expected)
{
  ASS_EQ(cc.getStatus(false), DecisionProcedure::SATISFIABLE);
  LiteralStack model;
  cc.getModel(model);
  ASS_EQ(model.size(), expected.size());
  for (auto literal : expected) {
    ASS(model.find(literal));
  }
}

// Both orderings reduce a = b, f(a) = c to a = b, f(min(a,b)) = c.
// The first instance can register fewer terms than the second one.
struct Fixture {
  TermList a, b, c, fa, fb, sort;

  Fixture()
  {
    DECL_SORT(srt)
    DECL_CONST(a, srt)
    DECL_CONST(b, srt)
    DECL_CONST(c, srt)
    DECL_FUNC(f, {srt}, srt)
    this->a = a;
    this->b = b;
    this->c = c;
    fa = f(a);
    fb = f(b);
    sort = a.sort();
  }

  Literal* eq(TermList lhs, TermList rhs)
  { return Literal::createEquality(true, lhs, rhs, sort); }

  void load(SimpleCongruenceClosure& cc, bool small = false)
  {
    cc.addLiteral(eq(a, b));
    if (!small) {
      cc.addLiteral(eq(fa, c));
      cc.addLiteral(eq(fb, fb));
    }
  }

  void check(SimpleCongruenceClosure& cc, const Ordering& ord, bool small = false)
  {
    if (small) {
      checkModel(cc, {eq(a, b)});
    } else {
      auto normal = ord.compare(a, b) == Ordering::Result::LESS ? fa : fb;
      ASS_EQ(ord.compare(normal, c), Ordering::Result::GREATER);
      checkModel(cc, {eq(a, b), eq(normal, c)});
    }
  }
};

}

TEST_FUN(two_live_instances)
{
  Fixture f;
  auto ord = ordering();
  SimpleCongruenceClosure first(&ord), second(&ord);
  f.load(first, true);
  f.check(first, ord, true);
  f.load(second);
  f.check(second, ord);
  f.check(first, ord, true);
}

TEST_FUN(two_live_orderings)
{
  Fixture f;
  auto ord = ordering();
  auto reverse = ordering(true);
  ASS_NEQ(ord.compare(f.a, f.b), reverse.compare(f.a, f.b));
  SimpleCongruenceClosure first(&ord), second(&reverse);
  f.load(first);
  f.load(second);
  f.check(first, ord);
  f.check(second, reverse);
  f.check(first, ord);
}

TEST_FUN(surviving_second_instance)
{
  Fixture f;
  auto ord = ordering();
  auto first = std::make_unique<SimpleCongruenceClosure>(&ord);
  SimpleCongruenceClosure second(&ord);
  f.load(*first, true);
  f.check(*first, ord, true);
  first.reset();
  f.load(second);
  f.check(second, ord);
}

TEST_FUN(repeated_extraction_and_reset)
{
  Fixture f;
  auto ord = ordering();
  SimpleCongruenceClosure cc(&ord);
  checkModel(cc, {});
  f.load(cc);
  f.check(cc, ord);
  f.check(cc, ord);
  cc.reset();
  checkModel(cc, {});
  f.load(cc, true);
  f.check(cc, ord, true);
}
