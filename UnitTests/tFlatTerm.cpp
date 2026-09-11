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
#include "Kernel/FlatTerm.hpp"

using namespace Kernel;

/**
 * FlatTerm::Entry::isOppositeFun relies on the fact that xor-ing a literal
 * header with 1 gives the header of the complementary literal (see
 * Literal::header/complementaryHeader in Kernel/Term.hpp). This test checks
 * that relationship holds for the header actually stored in a FlatTerm built
 * from a literal.
 */
TEST_FUN(isOppositeFun_matches_complementaryHeader) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt)
  DECL_CONST(a, srt)
  DECL_PRED(p, {srt})
  DECL_PRED(q, {srt})

  Literal* lit1 = p(a);
  Literal* lit2 = q(a);

  FlatTerm* ft1 = FlatTerm::create(TermList(lit1));
  FlatTerm* ft2 = FlatTerm::create(TermList(lit2));

  ASS((*ft1)[0].isOppositeFun(lit1->complementaryHeader()))
  ASS(!(*ft1)[0].isOppositeFun(lit1->header()))
  ASS((*ft1)[0].isFun(lit1->header()))
  ASS(!(*ft1)[0].isFun(lit1->complementaryHeader()))
  ASS(!(*ft1)[0].isOppositeFun(lit2->header()))
  ASS(!(*ft1)[0].isOppositeFun(lit2->complementaryHeader()))

  ASS((*ft2)[0].isOppositeFun(lit2->complementaryHeader()))
  ASS(!(*ft2)[0].isOppositeFun(lit2->header()))
  ASS((*ft2)[0].isFun(lit2->header()))
  ASS(!(*ft2)[0].isFun(lit2->complementaryHeader()))
  ASS(!(*ft2)[0].isOppositeFun(lit1->header()))
  ASS(!(*ft2)[0].isOppositeFun(lit1->complementaryHeader()))

  ft1->destroy();
  ft2->destroy();
}
