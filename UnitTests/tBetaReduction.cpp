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
#include "Shell/LambdaConversion.hpp"

TermList toDeBruijnIndices(TermList t){
  return LambdaConversion().convertLambda(t);
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////

TEST_FUN(beta_reduction01) {
  DECL_DEFAULT_VARS            
  DECL_SORT(srt)
  DECL_HOL_VAR(x0, 0, srt)
  DECL_CONST(a, srt)    
  DECL_CONST(b, srt)  

  BetaNormaliser bn;
  auto t = ap(lam(x0,x0),a);
  auto reduced = bn.normalise(toDeBruijnIndices(t));

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
  auto t = ap(lam(x0,ap(f, x0)),a);
  auto reduced = bn.normalise( toDeBruijnIndices(t));

  ASS_EQ(reduced, ap(f, a).sugaredExpr());
}

TEST_FUN(beta_reduction03) {            
  DECL_SORT(srt)
  DECL_ARROW_SORT(xSrt, {srt, srt})
  DECL_HOL_VAR(x, 0, xSrt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_CONST(a, srt)     

  BetaNormaliser bn;
  auto t = ap(  lam(x,ap(x,a)) , lam(y, y)  );
  auto reduced = bn.normalise(  toDeBruijnIndices(t)   );

  ASS_EQ(reduced, a.sugaredExpr());
}

TEST_FUN(beta_reduction04) {            
  DECL_SORT(srt)
  DECL_ARROW_SORT(xSrt, {srt, srt})
  DECL_HOL_VAR(x, 0, xSrt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_CONST(a, srt)     
  DECL_CONST(f, xSrt)     

  BetaNormaliser bn;
  auto t = ap(f,  ap(  lam(x,ap(x,a)) , lam(y, y)  )  );
  auto reduced = bn.normalise( toDeBruijnIndices(t)  );

  ASS_EQ(reduced, ap(f, a).sugaredExpr());
}

TEST_FUN(beta_reduction05) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_HOL_VAR(z, 2, srt)  

  BetaNormaliser bn;
  auto t = lam(x, ap(lam(y, lam(z, y) ), x)) ;
  auto res = lam(x,lam(z, x));
  auto reduced = bn.normalise( toDeBruijnIndices(t) );

  ASS_EQ(reduced, toDeBruijnIndices(res));
}

TEST_FUN(eta_reduction01) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_HOL_VAR(z, 2, srt)  
  DECL_ARROW_SORT(fSrt, {srt, srt, srt, srt})  
  DECL_CONST(f, fSrt)     

  EtaNormaliser en;
  auto t = lam(x, lam(y, lam(z, ap(ap(ap(f, x), y), z))));

  auto reduced = en.normalise( toDeBruijnIndices(t) );

  ASS_EQ(reduced, f.sugaredExpr());
}

TEST_FUN(eta_reduction02) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_HOL_VAR(z, 2, srt)  
  DECL_ARROW_SORT(fSrt, {srt, srt, srt, srt})  
  DECL_CONST(f, fSrt)     

  EtaNormaliser en;
  auto t = lam(x, lam(y, lam(z, ap(ap(ap(f, x), z), y))));
  auto tdb = toDeBruijnIndices(t);

  auto reduced = en.normalise( tdb );

  ASS_EQ(reduced, tdb);
}

TEST_FUN(eta_reduction03) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_HOL_VAR(z, 2, srt)  
  DECL_ARROW_SORT(fSrt, {srt, srt, srt, srt})  
  DECL_CONST(f, fSrt)     

  EtaNormaliser en;
  auto t = lam(x, lam(y, lam(z, ap(ap(ap(f, y), x), z))));
  auto tdb = toDeBruijnIndices(t);
  auto res = lam(x, lam(y, ap(ap(f, y), x) ));

  auto reduced = en.normalise( tdb );

  ASS_EQ(reduced, toDeBruijnIndices(res));
}

TEST_FUN(eta_reduction04) {            
  DECL_SORT(srt)
  DECL_ARROW_SORT(xSrt, {srt, srt, srt})    
  DECL_HOL_VAR(x, 0, xSrt)
  DECL_HOL_VAR(y, 1, srt)
  DECL_HOL_VAR(z, 2, srt)  

  EtaNormaliser en;
  auto t = lam(x, lam(y, lam(z, ap(ap(x, y), z))));
  auto tdb = toDeBruijnIndices(t);
  auto res = lam(x, x);

  auto reduced = en.normalise( tdb );

  ASS_EQ(reduced, toDeBruijnIndices(res));
}

TEST_FUN(eta_reduction05) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_ARROW_SORT(fSrt, {srt, srt, srt})  
  DECL_CONST(f, fSrt)     

  EtaNormaliser en;
  auto t = lam(x, ap(ap(f, x), x));
  auto tdb = toDeBruijnIndices(t);

  auto reduced = en.normalise( tdb );

  ASS_EQ(reduced, tdb);
}

TEST_FUN(eta_reduction06) {            
  DECL_SORT(srt)
  DECL_HOL_VAR(x, 0, srt)
  DECL_HOL_VAR(y, 1, srt)  
  DECL_ARROW_SORT(gSrt, {srt, srt}) 
  // TODO wierd stuff below...      
  DECL_ARROW_SORT(fSrt, {gSrt, srt, srt}) 
  DECL_CONST(f, fSrt)     
  DECL_CONST(g, gSrt)     

  EtaNormaliser en;
  auto t = lam(x, ap(ap(f, lam(y, ap(g, y))), x));
  auto tdb = toDeBruijnIndices(t);

  auto reduced = en.normalise( tdb );

  ASS_EQ(reduced, ap(f,g).sugaredExpr());
}
