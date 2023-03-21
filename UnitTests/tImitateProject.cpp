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
#include "Test/TestUtils.hpp"
#include "Test/GenerationTester.hpp"
#include "Shell/LambdaConversion.hpp"

#include "Inferences/ImitateProject.hpp"

using namespace Test;

REGISTER_GEN_TESTER(ImitateProject)

TermList dbs(TermList t){
  return LambdaConversion().convertLambda(t);
}

/**
 * NECESSARY: We neet to tell the tester which syntax sugar to import for creating terms & clauses. 
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_SORT(srt)                            \
  DECL_ARROW_SORT(xSrt, {srt, srt})         \
  DECL_ARROW_SORT(gSrt, {srt, srt, srt})    \
  DECL_HOL_VAR(x, 0, xSrt)                  \
  DECL_HOL_VAR(y, 2, srt)                   \
  DECL_HOL_VAR(z, 1, xSrt)                   \
  DECL_HOL_VAR(w, 3, gSrt)                   \
  DECL_HOL_VAR(k, 4, gSrt)                   \
  DECL_HOL_VAR(m, 5, gSrt)                   \
  DECL_HOL_VAR(p, 6, srt)                   \
  DECL_CONST(a, srt)                        \
  DECL_CONST(b, srt)                        \
  DECL_CONST(g, gSrt)                        \
  DECL_CONST(f, xSrt)                                                                                         \


/** Defines a test case. */
TEST_GENERATION(test_01,                                   // <- name
    Generation::TestCase()
      .options({ { "pretty_hol_printing", "pretty" } })   
      .input(     clause({  selected(a != ap(x, a))  })) // <- input clause
      .expected(exactly(                                   // <- a list of exactly which clauses are expected
            clause({  a != ap(dbs(lam(y,y)), a)  }),        
            clause({  a != ap(dbs(lam(y,a)), a)  })             //    to be returned. Order matters!
      ))
      .higherOrder(true)
    )

/** Defines a test case. */
TEST_GENERATION(test_02,                                   // <- name
    Generation::TestCase()
      .options({ { "pretty_hol_printing", "pretty" } })
      .input(     clause({  selected(ap(f, a) != ap(x, a))  })) // <- input clause
      .expected(exactly(                                   // <- a list of exactly which clauses are expected
            clause({ ap(f, a) != ap(dbs(lam(y,ap(f, ap(z, y)))), a)  })             //    to be returned. Order matters!
      ))
      .higherOrder(true)
    )

/** Defines a test case. */
TEST_GENERATION(test_03,                                   // <- name
    Generation::TestCase()
      .options({ { "pretty_hol_printing", "pretty" } })
      .input(     clause({  selected(ap(ap(g, a), b) != ap(ap(w, b), a))  })) // <- input clause
      .expected(exactly(                                   // <- a list of exactly which clauses are expected
            clause({ ap(ap(g, a), b) != ap(ap(  dbs(lam(y, lam(p, ap(ap(g, ap(ap(m, y), p) ), ap(ap(k, y), p)) ))), b ), a)  })             //    to be returned. Order matters!
      ))
      .higherOrder(true)      
    )