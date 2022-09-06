/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**!  This file contains examples on how to use Test/SyntaxSugar.hpp.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Kernel/ApplicativeHelper.hpp"

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(beta_reduction01) {
  DECL_DEFAULT_VARS            
  DECL_SORT(srt)
  DECL_HOL_VAR(x0, 0, srt)
  DECL_CONST(a, srt)    
  DECL_CONST(b, srt)  

  BetaNormaliser bn;
  auto reduced = bn.normalise(ap(lam(x0,x0),a));

  ASS_EQ(reduced, a.sugaredExpr());
}

TEST_FUN(beta_reduction02) {
  DECL_DEFAULT_VARS            
  DECL_SORT(srt)
  DECL_ARROW_SORT(fSrt, {srt, srt})
  DECL_HOL_VAR(x0, 0, srt)
  DECL_CONST(a, srt)    
  DECL_CONST(f,fSrt)  

  BetaNormaliser bn;
  auto reduced = bn.normalise(ap(lam(x0,ap(f, x0)),a));

  ASS_EQ(reduced, ap(f, a).sugaredExpr());
}

TEST_FUN(beta_reduction03) {            
  DECL_SORT(srt)
  DECL_ARROW_SORT(xSrt, {srt, srt})
  DECL_HOL_VAR(x, 0, xSrt)
  DECL_HOL_VAR(y, 0, srt)
  DECL_CONST(a, srt)     

  BetaNormaliser bn;
  auto reduced = bn.normalise(   ap(  lam(x,ap(x,a)) , lam(y, y)  )    );

  ASS_EQ(reduced, a.sugaredExpr());
}

TEST_FUN(beta_reduction04) {            
  DECL_SORT(srt)
  DECL_ARROW_SORT(xSrt, {srt, srt})
  DECL_HOL_VAR(x, 0, xSrt)
  DECL_HOL_VAR(y, 0, srt)
  DECL_CONST(a, srt)     
  DECL_CONST(f, xSrt)     

  BetaNormaliser bn;
  auto reduced = bn.normalise( ap(f,  ap(  lam(x,ap(x,a)) , lam(y, y)  )  )  );

  ASS_EQ(reduced, ap(f, a).sugaredExpr());
}

TEST_FUN(beta_reduction05) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 0, srt)
  DECL_HOL_VAR(z, 0, srt)  

  BetaNormaliser bn;
  auto reduced = bn.normalise( lam(x, ap(lam(y, lam(z, y) ), x))  );

  ASS_EQ(reduced, lam(x,lam(z, x)).sugaredExpr());
}