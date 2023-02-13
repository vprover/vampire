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
#include "Kernel/KBO.hpp"
#include "Kernel/SKIKBO.hpp"
#include "Kernel/Ordering.hpp"
#include "tKBO.hpp"

//////////////////////////////////////////////////////////////////////////////// 
/////////////////////////////// HELPER FUNCTIONS /////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////// 

using namespace Kernel;

SKIKBO skikbo(unsigned introducedSymbolWeight, 
    unsigned variableWeight, 
    const Map<unsigned, KboWeight>& symbolWeights) {
 
  return SKIKBO(toWeightMap<FuncSigTraits>(introducedSymbolWeight, 
                  { 
                    ._variableWeight = variableWeight ,
                    ._numInt  = variableWeight,
                    ._numRat  = variableWeight,
                    ._numReal = variableWeight,
                  }, 
                symbolWeights, env.signature->functions()),
                DArray<int>::fromIterator(getRangeIterator(0, (int) env.signature->functions())),
                DArray<int>::fromIterator(getRangeIterator(0, (int) env.signature->typeCons())),
                DArray<int>::fromIterator(getRangeIterator(0, (int) env.signature->predicates())),
                predLevels(),                
                /*revereseLCM*/ false);
}


SKIKBO skikbo(const Map<unsigned, KboWeight>& symbolWeights) {
  return skikbo(1, 1, symbolWeights);
}

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// TEST CASES //////////////////////////////////
//
// How to read the test cases in this file:
//
TEST_FUN(skikbo_test01) {
  DECL_DEFAULT_VARS             // <- macro to initialize some syntax sugar for creating terms over a single uninterpreted sort  
  DECL_SORT(srt)
  DECL_ARROW_SORT(xSrt, {srt, srt})
  DECL_HOL_VAR(x0, 0, xSrt)
  DECL_CONST(a, srt)    // <- declares a constant symbol
  DECL_CONST(b, srt)    // <- declares a constant symbol  

  // !!! The declaration order of function and constant symbols will define their precedence relation !!!
  auto ord = skikbo( 
      weights( // <- function symbol weights
        make_pair(a, 10u), // <- sets the weight of the function f to 10
        make_pair(b, 1u ) // <- sets the weight of the constant c to 1
        // other functions/constants default to weight 1
      )      
  ); 

  env.options->useCombSup();

  ASS_EQ(ord.compare(ap(x0,a), ap(x0,b)), Ordering::Result::GREATER)
}
//
//
//
////////////////////////////////////////////////////////////////////////////////

TEST_FUN(skikbo_test02) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt, srt})
  DECL_HOL_VAR(x0, 0, xSrt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = skikbo(
    weights(
      make_pair(a, 2u),
      make_pair(b, 1u)     
    )
  );

  env.options->useCombSup();

  ASS_EQ(ord.compare(ap(ap(x0, a), b), ap(ap(x0, b), a)), Ordering::Result::GREATER)
}

TEST_FUN(skikbo_test03) {
  DECL_DEFAULT_VARS
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt, srt})  
  DECL_HOL_VAR(x0, 0, xSrt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)

  auto ord = skikbo(
    weights(
      make_pair(a, 1u),
      make_pair(b, 1u)     
    )
  );

  env.options->useCombSup();

  ASS_EQ(ord.compare(ap(ap(x0, b), a), ap(ap(x0, a), b)), Ordering::Result::GREATER)
}

TEST_FUN(skikbo_test04) {
  DECL_DEFAULT_VARS
  DECL_COMBINATORS  
  DECL_SORT(srt) 
  DECL_ARROW_SORT(fSrt, {srt, srt, srt, srt})  
  DECL_CONST(a, srt)
  DECL_CONST(f, fSrt)

  auto ord = skikbo(
    weights(
      make_pair(f, 10u),
      make_pair(a, 1u)     
    )
  );

  env.options->useCombSup();

  ASS_EQ(ord.compare(ap(I(srt), a), ap(ap(ap(f, a), a), a)), Ordering::Result::GREATER)
}

TEST_FUN(skikbo_test05) {
  DECL_DEFAULT_VARS
  DECL_COMBINATORS  
  DECL_SORT(srt) 
  DECL_ARROW_SORT(xSrt, {srt, srt}) 
  DECL_ARROW_SORT(fSrt, {srt, srt, srt}) 
  DECL_HOL_VAR(x0, 0, xSrt)
  DECL_CONST(a, srt)
  DECL_CONST(b, srt)
  DECL_CONST(f, fSrt)

  auto ord = skikbo(
    weights(
      make_pair(f, 10u),
      make_pair(a, 2u),
      make_pair(b, 1u)           
    )
  );

  //f (x0 a) (S x y a)
  auto t1 = ap(ap(f, ap(x0, a)),  ap(ap(ap(S(srt, srt, srt), x), y), a) );
  //f (x0 b) (S x y b)
  auto t2 = ap(ap(f, ap(x0, b)),  ap(ap(ap(S(srt, srt, srt), x), y), b) );

  env.options->useCombSup();

  ASS_EQ(ord.compare(t1, t2), Ordering::Result::GREATER)
}

TEST_FUN(skikbo_test06) {
  DECL_DEFAULT_VARS
  DECL_DEFAULT_SORT_VARS  
  DECL_SORT(srt1)
  DECL_TYPE_CON(list, 1)
  DECL_ARROW_SORT(fSrt, {srt1, srt1}) 
  DECL_CONST(a, srt1)
  DECL_POLY_CONST(f, 1, fSrt)

  auto ord = skikbo(
    weights(
      make_pair(f, 10u),
      make_pair(a, 2u)                         
    )
  );

  // f<list(srt1)>(a)
  auto t1 = ap(f(list(srt1)), a);
  // f<srt1>(a)
  auto t2 = ap(f(srt1), a);

  env.options->useCombSup();

  ASS_EQ(ord.compare(t1, t2), Ordering::Result::GREATER)
}
