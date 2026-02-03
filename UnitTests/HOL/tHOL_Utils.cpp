/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */



#include "Test/HOLUtils.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Test/UnitTesting.hpp"

using namespace Test::HOL;

std::vector<TermList> mkSorts(unsigned n) {
  std::string sortPrefix = "srt";
  std::vector<TermList> sorts;
  for (unsigned i = 0; i < n; ++i)
    sorts.push_back(mkAtomicSort(sortPrefix + std::to_string(i)));

  return sorts;
}

HOL_TEST_FUN(hol_utils_getNthArg) {
  assertThrows([&D] { HOL::getNthArg(D.fSrt, 0); }, "argNum > 0");
  assertThrows([&D] { HOL::getNthArg(D.srt, 1); }, "arrowSort.isArrowSort()");

  constexpr unsigned N = 10;
  for (unsigned n = 1; n <= N; ++n) {
    const auto sorts = mkSorts(n);
    auto srt = AtomicSort::arrowSort(sorts.size(), sorts.data(), D.srt);

    ASS_EQ(HOL::getArity(srt), n)

    for (unsigned i = 0; i < n; ++i)
      ASS_EQ(HOL::getNthArg(srt, i+1), sorts[i])

  }
}

HOL_TEST_FUN(hol_utils_getResultAppliedToNArgs) {
  assertThrows([&D] { HOL::getResultAppliedToNArgs(D.srt, 1); }, "arrowSort.isArrowSort()");
  assertThrows([&D] { HOL::getResultAppliedToNArgs(D.fSrt, 2); }, "arrowSort.isArrowSort()");

  ASS_EQ(HOL::getResultAppliedToNArgs(D.fSrt, 0), D.fSrt)

  constexpr unsigned N = 10;
  for (unsigned n = 1; n <= N; ++n) {
    const auto sorts = mkSorts(n);
    auto srt = AtomicSort::arrowSort(sorts.size(), sorts.data(), D.srt);

    for (unsigned i = 0; i < n; ++i)
      ASS_EQ(HOL::getResultAppliedToNArgs(srt, i), AtomicSort::arrowSort(sorts.size()-i, sorts.data()+i, D.srt))

    ASS_EQ(HOL::getResultAppliedToNArgs(srt, n), D.srt)
    assertThrows([&srt, &n] { HOL::getResultAppliedToNArgs(srt, n+1); }, "arrowSort.isArrowSort()");
  }
}
