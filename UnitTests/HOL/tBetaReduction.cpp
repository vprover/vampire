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

HOL_TEST_FUN(beta_reduction_1) {
  const std::initializer_list<TermList> testTerms { // all terms are of type srt
    D.a, x(0), x(1), app(D.f, D.a), app(D.f, x(0)), app(D.f, app(D.f, x(0)))
  };

  unsigned reds;
  for (const auto term : testTerms) {
    auto reduced = betaNF(
      toNameless(app(id(), {term, D.srt})), &reds
    );

    ASS_EQ(reds, 1)
    ASS_EQ(reduced, term)
    ASS_EQ(reduced.toString(), term.toString())
  }
}

HOL_TEST_FUN(beta_reduction_2) {
  const std::initializer_list<TermList> testTerms { // all terms are of type srt
    D.a, x(0), x(1), app(D.f, D.a), app(D.f, x(1)), app(D.f, app(D.f, x(1)))
  };

  unsigned reds;
  for (const auto term1 : testTerms) {
    if (term1 == x(0))
      continue;

    for (const auto term2 : testTerms) {
      auto constFn = lam(x(0), {term1, D.srt});
      auto reduced = betaNF(
        toNameless(app(constFn, {term2, D.srt})), &reds
      );

      ASS_EQ(reds, 1)
      ASS_EQ(reduced, term1)
      ASS_EQ(reduced.toString(), term1.toString())
    }
  }
}

HOL_TEST_FUN(beta_reduction_3) {
  std::vector<TermList> testTerms {
    D.a, x(0), x(1), app(D.f, D.a), app(D.f, x(1)), app(D.f, app(D.f, x(1)))
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

    for (auto& testTerm : testTerms)
      testTerm = lam(x(i), {testTerm, termSort});
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

HOL_TEST_FUN(beta_reduction_4) {
  // (λ x0:(α -> α). x0 a) (λ x0:α. x0)
  auto term = app(lam(x(0, D.fSrt), app(x(0, D.fSrt), D.a)), id());

  auto t1 = toNameless(term);
  ASS_EQ(termListToString(t1, Options::HPrinting::TPTP),
         "((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0)))")
  ASS_EQ(termListToString(t1, Options::HPrinting::RAW),
         "vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt)))")

  unsigned reds;
  ASS_EQ(betaNF(t1, &reds), D.a)
  ASS_EQ(reds, 2)

  auto t2 = toNameless(app(D.f, term));
  ASS_EQ(termListToString(t2, Options::HPrinting::TPTP),
         "(f @ ((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0))))")
  ASS_EQ(termListToString(t2, Options::HPrinting::RAW),
         "vAPP(srt,srt,f,vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt))))")
  ASS_EQ(betaNF(t2, &reds), app(D.f, D.a))
  ASS_EQ(reds, 2)

  auto t3 = toNameless(app(lam(x(0), D.f), term));
  ASS_EQ(termListToString(t3, Options::HPrinting::TPTP),
         "((^[Y0 : srt]: (f)) @ ((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0))))")
  ASS_EQ(termListToString(t3, Options::HPrinting::RAW),
         "vAPP(srt,srt > srt,vLAM(srt,srt > srt,f),vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt))))")
  ASS_EQ(betaNF(t3, &reds), D.f)
  ASS_EQ(reds, 1)

  auto t4 = toNameless(app(id(), term));
  ASS_EQ(termListToString(t4, Options::HPrinting::TPTP),
         "((^[Y0 : srt]: (Y0)) @ ((^[Y0 : srt > srt]: (Y0 @ a)) @ (^[Y0 : srt]: (Y0))))")
  ASS_EQ(termListToString(t4, Options::HPrinting::RAW),
         "vAPP(srt,srt,vLAM(srt,srt,db0(srt)),vAPP(srt > srt,srt,vLAM(srt > srt,srt,vAPP(srt,srt,db0(srt > srt),a)),vLAM(srt,srt,db0(srt))))")
  ASS_EQ(betaNF(t4, &reds), D.a)
  ASS_EQ(reds, 3)
}