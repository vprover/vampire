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
#include "Kernel/HOL/TermShifter.hpp"
#include "Test/UnitTesting.hpp"
#include "Test/HOLUtils.hpp"

using namespace Test::HOL;

const auto shift = TermShifter::shift;

std::pair<TermList, Option<unsigned>> termWithIndex(TermList t, unsigned i) {
  return {t, Option<unsigned>(i)};
}

std::pair<TermList, Option<unsigned>> termOnly(TermList t) {
  return {t, Option<unsigned>()};
}

HOL_TEST_FUN(term_shifter_1) {
  const std::initializer_list<TermList> testTerms { // all terms are of type srt
    D.a, x(0), x(1), app(D.f, D.a), app(D.f, x(0)), app(D.f, app(D.f, x(0)))
  };

  for (const auto term : testTerms) {
    auto lambdaTerm = HOL::convert::toNameless(lam(x(0), {term, D.srt}));

    ASS_EQ(
      shift(lambdaTerm, 1),
      termOnly(lambdaTerm)
    )
  }
}

HOL_TEST_FUN(term_shifter_2) {
  ASS_EQ(
    shift(db(1), 1),
    termWithIndex(db(2), 1)
  )

  ASS_EQ(
    shift(db(1, D.srt), -1),
    termWithIndex(db(0), 1)
  )

  ASS_EQ(
    shift(app(db(1, D.fSrt), db(2, D.srt)), -1),
    termWithIndex(app(db(0, D.fSrt), db(1, D.srt)), 1)
  )
}

HOL_TEST_FUN(term_shifter_3) {
  auto term = LAM(D.srt, app(D.f, db(0)));
  ASS_EQ(
    shift(term, 1),
    termOnly(term)
  )

  for (unsigned i = 1; i < 5; ++i) {
    ASS_EQ(
      shift(LAM(D.srt, app(D.f, db(i))), 1),
      termWithIndex(LAM(D.srt, app(D.f, db(i+1))), i-1)
    )
  }
}

HOL_TEST_FUN(term_shifter_4) {
  ASS_EQ(
    shift(app(LAM(D.srt, app(D.f, db(0))), app(D.f, db(0))), 1),
    termWithIndex(app(LAM(D.srt, app(D.f, db(0))), app(D.f, db(1))), 0)
  )

  ASS_EQ(
    shift(app(LAM(D.srt, app(D.f, db(0))), app(D.f, db(1))), -1),
    termWithIndex(app(LAM(D.srt, app(D.f, db(0))), app(D.f, db(0))), 1)
  )

  auto term = LAM(D.srt, app(LAM(D.srt, app(D.f, db(0))), app(D.f, db(0))));
  ASS_EQ(
    shift(term, 1),
    termOnly(term)
  )
}