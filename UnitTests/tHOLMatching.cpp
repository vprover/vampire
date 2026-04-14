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
#include "Kernel/HOL/Matcher.hpp"

using namespace Test;
using namespace Indexing;

#define MY_SUGAR                        \
  DECL_DEFAULT_VARS                     \
  DECL_SORT(srt)                        \
  DECL_CONST(a, srt)                    \
  DECL_CONST(b, srt)                    \
  DECL_CONST(f, arrow(srt, srt))        \
  DECL_CONST(g, arrow({srt, srt}, srt))

void check(TermSugar base, TermSugar instance, bool shouldMatch)
{
  if (Kernel::HOL::Matcher::matches(base, instance) == shouldMatch) {
    std::cout << "[  OK  ] " << base << (shouldMatch ? " == " : " != ") << instance << std::endl;
  } else {
    std::cout << std::endl;
    std::cout << "[ FAIL ] " << base << (shouldMatch ? " == " : " != ") << instance << std::endl;
    ASSERTION_VIOLATION;
  }
}

#define TEST_MATCHES(name, base, instance) \
  TEST_FUN(name) {                         \
    __ALLOW_UNUSED(MY_SUGAR);              \
    env.setHigherOrder(true);              \
    check(base, instance, true);           \
  }

#define TEST_DOES_NOT_MATCH(name, base, instance) \
  TEST_FUN(name) {                                \
    __ALLOW_UNUSED(MY_SUGAR);                     \
    env.setHigherOrder(false);                    \
    check(base, instance, false);                 \
  }

TEST_MATCHES(success01, x.sort(srt), b);
TEST_MATCHES(success02, ap(f, x), ap(f, ap(f, a)));
TEST_MATCHES(success03, ap(x.sort(arrow(srt,srt)), a), b);
TEST_MATCHES(success04, ap(x.sort(arrow(arrow(srt, srt), srt)), lam(srt, db(0, srt))), a);
TEST_MATCHES(success05, ap(g, {ap(x.sort(arrow(srt,srt)), a), ap(x.sort(arrow(srt,srt)), b)}), ap(g, {a, b}));

TEST_DOES_NOT_MATCH(fail01, a, b);
TEST_DOES_NOT_MATCH(fail02, b, x.sort(srt));
TEST_DOES_NOT_MATCH(fail03, x.sort(srt), db(0, srt));
