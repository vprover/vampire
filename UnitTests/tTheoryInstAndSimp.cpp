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
#include "Inferences/TheoryInstAndSimp.hpp"

using namespace Inferences;

#define UNIT_ID TheoryInstAndSimp
UT_CREATE;

TEST_FUN(test_pure) {
  THEORY_SYNTAX_SUGAR(REAL)

  Literal& lit = lt(0, mul(x, frac(7,1)));
  auto th = TheoryInstAndSimp();

  ASS(th.isPure(&lit));
}
