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
using HOL::convert::toNameless;
using HOL::create::namelessLambda;

const auto shift = TermShifter::shift;

TypedTermList db(int index, std::optional<TermList> sort = std::nullopt) {
  TermList s = sort.value_or(Defs::instance()->srt);
  return {HOL::getDeBruijnIndex(index, s), s};
}

HOL_TEST_FUN(term_shifter_1) {
  const std::initializer_list<TermList> testTerms { // all terms are of type srt
    D.a, x(0), x(1), app(D.f, D.a), app(D.f, x(0)), app(D.f, app(D.f, x(0)))
  };

  for (const auto term : testTerms) {
    auto lambdaTerm = toNameless(lam(x(0), {term, D.srt}));

    auto [result, mfi] = shift(lambdaTerm, 1);
    ASS_EQ(result, lambdaTerm)
    ASS(mfi.isNone())
  }
}

HOL_TEST_FUN(term_shifter_2) {
  auto res = shift(db(1), 1);
  ASS(res.second == Option<unsigned>(1))
  ASS_EQ(res.first, db(2))

  res = shift(db(1, D.srt), -1);
  ASS(res.second == Option<unsigned>(1))
  ASS_EQ(res.first, db(0, D.srt))

  res = shift(app(db(1, D.fSrt), db(2, D.srt)), -1);
  ASS(res.second == Option<unsigned>(1))
  ASS_EQ(res.first, app(db(0, D.fSrt), db(1, D.srt)))
}

HOL_TEST_FUN(term_shifter_3) {
  auto term = namelessLambda(D.srt, D.srt, app(D.f, db(0)));
  auto res = shift(term, 1);
  ASS(res.second.isNone())
  ASS_EQ(res.first, term)

  for (unsigned i = 1; i < 5; ++i) {
    term = namelessLambda(D.srt, D.srt, app(D.f, db(i)));
    res = shift(term, 1);
    ASS(res.second == Option<unsigned>(i-1))
    ASS_EQ(res.first, namelessLambda(D.srt, D.srt, app(D.f, db(i+1))))
  }
}