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
using HOL::convert::toNameless;
using HOL::reduce::betaNF;



TEST_FUN(beta_reduction_1) {
  env.setHigherOrder(true);
  const auto& D = *Defs::instance();

  auto id = lam({D.x0, D.srt}, {D.x0, D.srt});


  const std::initializer_list<TermList> testTerms { // all terms are of type srt
    D.a, D.x0, D.x1, app(D.f, D.a), app(D.f, {D.x0, D.srt}), app(D.f, app(D.f, {D.x0, D.srt}))
  };

  unsigned reds;
  for (const auto term : testTerms) {
    auto reduced = betaNF(
      toNameless(app(id, {term, D.srt})), &reds
    );

    ASS_EQ(reds, 1)
    ASS_EQ(reduced, term)
    ASS_EQ(reduced.toString(), term.toString())
  }
}

TEST_FUN(beta_reduction_2) {
  env.setHigherOrder(true);
  const auto& D = *Defs::instance();

  const std::initializer_list<TermList> testTerms { // all terms are of type srt
    D.a, D.x0, D.x1, app(D.f, D.a), app(D.f, {D.x1, D.srt}), app(D.f, app(D.f, {D.x1, D.srt}))
  };

  unsigned reds;
  for (const auto term1 : testTerms) {
    if (term1 == D.x0)
      continue;

    for (const auto term2 : testTerms) {
      auto constFn = lam({D.x0, D.srt}, {term1, D.srt});
      auto reduced = betaNF(
        toNameless(app(constFn, {term2, D.srt})), &reds
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
    D.a, D.x0, D.x1, app(D.f, D.a), app(D.f, {D.x1, D.srt}), app(D.f, app(D.f, {D.x1, D.srt}))
  };

  unsigned reds;
  for (const auto term : testTerms) {
    auto t2 = toNameless(term);
    ASS(term == t2 && term.toString() == t2.toString())

    auto reduced = betaNF(term, &reds);

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

      auto reduced = betaNF(t2, &reds);

      ASS_EQ(reds, 0)
      ASS_EQ(reduced, t2)
      ASS_EQ(reduced.toString(), t2.toString())
    }
  }
}

TEST_FUN(beta_reduction_4) {
  env.setHigherOrder(true);
  const auto& D = *Defs::instance();

  // (λ x0:(α -> α). x0 a) (λ x0:α. x0)
  auto term = app(lam({D.x0, D.fSrt}, {app({D.x0, D.fSrt}, D.a), D.srt}), lam({D.x0, D.srt}, {D.x0, D.srt}));

  auto t1 = toNameless(term);
  ASS_EQ(termListToString(t1, Options::HPrinting::TPTP),
         "(^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0))")
  ASS_EQ(termListToString(t1, Options::HPrinting::RAW),
         "vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt)))")

  unsigned reds;
  ASS_EQ(betaNF(t1, &reds), D.a)
  ASS_EQ(reds, 2)

  auto t2 = toNameless(app(D.f, term));
  ASS_EQ(termListToString(t2, Options::HPrinting::TPTP),
         "f @ ((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0)))")
  ASS_EQ(termListToString(t2, Options::HPrinting::RAW),
         "vAPP(srt,srt,f,vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt))))")
  ASS_EQ(betaNF(t2, &reds), app(D.f, D.a))
  ASS_EQ(reds, 2)

  auto t3 = toNameless(app(lam({D.x0, D.srt}, D.f), term));
  ASS_EQ(termListToString(t3, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: (f)) @ ((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0)))")
  ASS_EQ(termListToString(t3, Options::HPrinting::RAW),
         "vAPP(srt,srt > srt,vLAM(srt,srt > srt,f),vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt))))")
  ASS_EQ(betaNF(t3, &reds), D.f)
  ASS_EQ(reds, 1)

  auto t4 = toNameless(app(lam({D.x0, D.srt}, {D.x0, D.srt}), term));
  ASS_EQ(termListToString(t4, Options::HPrinting::TPTP),
         "(^[Y0 : srt]: (Y0)) @ ((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0)))")
  ASS_EQ(termListToString(t4, Options::HPrinting::RAW),
         "vAPP(srt,srt,vLAM(srt,srt,db0(srt)),vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt))))")
  ASS_EQ(betaNF(t4, &reds), D.a)
  ASS_EQ(reds, 3)
}