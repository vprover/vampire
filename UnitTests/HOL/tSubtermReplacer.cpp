/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Kernel/HOL/HOL.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/HOLUtils.hpp"

using namespace Test::HOL;

HOL_TEST_FUN(subterm_replacer_1) {
  auto term = app(D.f, x(0));
  auto idFun = LAM(D.srt, db(0));

  ASS_EQ(
    term.replaceSubterm(D.f, idFun),
    app(LAM(D.srt, db(0)), x(0))
  )

  ASS_EQ(
    term.replaceSubterm(x(0), term),
    app(D.f, term)
  )
}

HOL_TEST_FUN(subterm_replacer_2) {
  auto term = LAM(D.srt, app(D.f, x(0)));

  ASS_EQ(
    term.replaceSubterm(x(0), db(0)),
    LAM(D.srt, app(D.f, db(0)))
  )

  ASS_EQ(
    term.replaceSubterm(x(0), db(0), true),
    LAM(D.srt, app(D.f, db(1)))
  )
}