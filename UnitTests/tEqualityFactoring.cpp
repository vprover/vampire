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

#include "Inferences/EqualityFactoring.hpp"

using namespace Test;

REGISTER_GEN_TESTER(EqualityFactoring)

/**
 * NECESSARY: We neet to tell the tester which syntax sugar to import for creating terms & clauses. 
 * See Test/SyntaxSugar.hpp for which kinds of syntax sugar are available
 */
#define MY_SYNTAX_SUGAR                                                                                       \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_DEFAULT_SORT_VARS                                                                                      \
  DECL_SORT(s)                                                                                                \
  DECL_SORT(s2)                                                                                               \
  DECL_FUNC(f, {s}, s)                                                                                        \
  DECL_FUNC(g, {s}, s)                                                                                        \
  DECL_TYPE_CON(list, 1)                                                                                      \
  DECL_POLY_CONST(poly_list, 1, {list(alpha)})                                                                \
  DECL_POLY_CONST(j, 1, {list(alpha)})                                                                        \
  DECL_CONST(a, s)                                                                                            \
  DECL_PRED (p, {s})                                                                                          \
  DECL_PRED (q, {s})                                                                                          \
  DECL_VAR(k, 3)                                                                                              \

TEST_GENERATION(test_01,                                   // <- name
    Generation::TestCase()
      .input(     clause({  selected(poly_list(alpha) == j(alpha)), j(s) == poly_list(s)  })) // <- input clause
      .expected(exactly(                                   // <- a list of exactly which clauses are expected
            clause({  j(s) == poly_list(s), poly_list(s) != poly_list(s) })                          //    to be returned. Order matters!
      ))
      .polymorphic(true)
    )

TEST_GENERATION(test_02,
    Generation::TestCase()
      .input(     clause({  selected(x.sort(s2) == y), z.sort(s) == k  })) 
      .expected(exactly(                                
      ))
      .polymorphic(true)
    )