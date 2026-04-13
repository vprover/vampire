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
#include "Kernel/Matcher.hpp"

using namespace Test;
using namespace Indexing;

TEST_FUN(basic01) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(f, arrow(srt, srt))

  ASS(!MatchingUtils::matchTermsHOL(a, b));
  ASS(MatchingUtils::matchTermsHOL(x.sort(srt), b));
  ASS(!MatchingUtils::matchTermsHOL(b, x.sort(srt)));
  ASS(MatchingUtils::matchTermsHOL(ap(f, x), ap(f, ap(f, a))));
  ASS(MatchingUtils::matchTermsHOL(ap(x.sort(arrow(srt,srt)), a), b));
  ASS(MatchingUtils::matchTermsHOL(ap(x.sort(arrow(arrow(srt, srt), srt)), lam(srt, db(0, srt))), a));
}
