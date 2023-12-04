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
#include "Kernel/RobSubstitution.hpp"

using namespace Kernel;

void check(TermList t1, TermList t2) {
  RobSubstitution subs;
  ASS(subs.match(t1, 0, t2, 1))
}

TEST_FUN(test_match1) {
  DECL_DEFAULT_VARS
  DECL_SORT(s);
  DECL_FUNC(f, {s, s}, s);
  DECL_CONST(a, s)
  DECL_CONST(b, s)
  check(f(f(a, y), f(x, b)), f(f(a,b),f(a,b)));

}
