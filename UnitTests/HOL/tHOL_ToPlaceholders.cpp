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
#include "Test/HOLUtils.hpp"
#include "Test/UnitTesting.hpp"

using namespace Test::HOL;

TypedTermList ph(TermList sort) {
  return {HOL::create::placeholder(sort), sort};
}

HOL_TEST_FUN(to_placeholders_1) {
  auto term = app({D.h, D.f, app(x(1, D.fSrt), x(2))});
  ASS_EQ(term.sort(), D.srt)

  ASS_EQ(
    termListToString(term, Options::HPrinting::TPTP),
    "(h @ f @ (X1 @ X2))"
  )

  ASS_EQ(
    termListToString(term, Options::HPrinting::RAW),
    "vAPP(srt,srt,vAPP(srt > srt,srt > srt,h,f),vAPP(srt,srt,X1,X2))"
  )

  ASS_EQ(
    HOL::toPlaceholders(term),
    app({D.h, ph(D.fSrt), ph(D.srt)})
  )

  ASS_EQ(
    HOL::toPlaceholders(term, Options::FunctionExtensionality::OFF),
    app({D.h, D.f, ph(D.srt)})
  )
}

HOL_TEST_FUN(to_placeholders_2) {
  ASS_EQ(
    HOL::toPlaceholders(app({D.h, LAM(D.srt, db(0)), D.a})),
    app({D.h, ph(D.fSrt), D.a})
  )
}