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
using HOL::create::app;
using HOL::convert::toNameless;

TEST_FUN(beta_reduction_1) {
  env.setHigherOrder(true);
  const auto& D = *Defs::instance();

  auto id = lam({D.x0, D.srt}, {D.x0, D.srt});

  const std::initializer_list<TermList> testTerms {
    D.a, D.x0, D.x1, app(D.srt, D.srt, D.f, D.a), app(D.srt, D.srt, D.f, D.x0), app(D.srt, D.srt, D.f, app(D.srt, D.srt, D.f, D.x0))
  };

  unsigned reds;
  for (const auto term : testTerms) {
    auto reduced = HOL::reduce::betaNF(
      toNameless(app(D.srt, D.srt, id, term)), &reds
    );

    ASS_EQ(reds, 1)
    ASS_EQ(reduced, term)
    ASS_EQ(reduced.toString(), term.toString())
  }
}

TEST_FUN(beta_reduction_2) {
  env.setHigherOrder(true);
  const auto& D = *Defs::instance();

  const std::initializer_list<TermList> testTerms {
    D.a, D.x0, D.x1, app(D.srt, D.srt, D.f, D.a), app(D.srt, D.srt, D.f, D.x1), app(D.srt, D.srt, D.f, app(D.srt, D.srt, D.f, D.x1))
  };

  unsigned reds;
  for (const auto term1 : testTerms) {
    if (term1 == D.x0)
      continue;

    for (const auto term2 : testTerms) {
      auto constFn = lam({D.x0, D.srt}, {term1, D.srt});
      auto reduced = HOL::reduce::betaNF(
        toNameless(app(D.srt, D.srt, constFn, term2)), &reds
      );

      ASS_EQ(reds, 1)
      ASS_EQ(reduced, term1)
      ASS_EQ(reduced.toString(), term1.toString())
    }
  }
}

TEST_FUN(beta_reduction_3) {
  env.setHigherOrder(true);
  const auto& D = *Defs::instance();

  std::vector<TermList> testTerms {
    D.a, D.x0, D.x1, app(D.srt, D.srt, D.f, D.a), app(D.srt, D.srt, D.f, D.x1), app(D.srt, D.srt, D.f, app(D.srt, D.srt, D.f, D.x1))
  };

  unsigned reds;
  for (const auto term : testTerms) {
    auto t2 = toNameless(term);
    ASS(term == t2 && term.toString() == t2.toString())

    auto reduced = HOL::reduce::betaNF(
      term, &reds
    );

    ASS_EQ(reds, 0)
    ASS_EQ(reduced, term)
    ASS_EQ(reduced.toString(), term.toString())
  }

  auto termSort = D.srt;
  for (unsigned i = 0; i < 10; ++i) {
    for (auto& testTerm : testTerms) {
      testTerm = lam({TermList::var(i), D.srt}, {testTerm, termSort});
    }
    termSort = TermList(AtomicSort::arrowSort(D.srt, termSort));

    for (const auto term : testTerms) {

      auto t2 = toNameless(term);
      ASS(term != t2 && term.toString() != t2.toString())

      auto reduced = HOL::reduce::betaNF(
        t2, &reds
      );

      ASS_EQ(reds, 0)
      ASS_EQ(reduced, t2)
      ASS_EQ(reduced.toString(), t2.toString())
    }
  }
}