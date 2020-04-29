/**!  This file contains examples on how to use Test/SyntaxSugar.hpp.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#define UNIT_ID SyntaxSugar
UT_CREATE;

template<class A>
void perform_test(const A&) { 
  /* dummy function to get rid of warnings */ 
}

TEST_FUN(some_meaningful_testname) {
  THEORY_SYNTAX_SUGAR(REAL)

  Literal& lit = neg(lt(0, mul(x, frac(7,1))));

  perform_test(lit);
}

TEST_FUN(some_other_meaningful_testname) {
  THEORY_SYNTAX_SUGAR(REAL)

  TermList t = mul(x, frac(7,3));

  perform_test(t);
}



