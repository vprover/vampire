/**!  This file contains examples on how to use Test/SyntaxSugar.hpp.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"

#define UNIT_ID SyntaxSugar
UT_CREATE;

template<class... A>
void perform_test(const A&...) { 
  /* dummy function to get rid of warnings */ 
}

TEST_FUN(some_meaningful_testname) {
  THEORY_SYNTAX_SUGAR(REAL) /* <-- imports syntax sugar */

  Literal* lit = ~(0 < (x * frac(7,1)));

  perform_test(lit);
}

TEST_FUN(some_other_meaningful_testname) {
  THEORY_SYNTAX_SUGAR(RAT)

  TermList t = x * frac(7,3);

  perform_test(t);
}


TEST_FUN(add_uninterpreted_stuff) {
  THEORY_SYNTAX_SUGAR(RAT) /* <-- imports syntax sugar */
  THEORY_SYNTAX_SUGAR_FUN (fn,       2) /* <-- creates an uninterpreted  function over the rational sort with arity 2 */
  THEORY_SYNTAX_SUGAR_PRED(relation, 2) /* <-- creates an uninterpreted predicate over the rational sort with arity 2 */

  Literal* t = relation(x, fn(frac(7,3), x));

  perform_test(t);
}

TEST_FUN(watch_out_for_this) {
  THEORY_SYNTAX_SUGAR(REAL)
  THEORY_SYNTAX_SUGAR_PRED(p, 1) 

  /* 
   * !!!!! watch out for bugs like this !!!! 
   *
   * If there are only integer literals and no predicates, functions or variables involved the 
   * compiler will treat expressions as integers, and not as terms.
   *
   * In order to circumvent this you can explicitly turn c++ integer literals into terms using the function
   * num
   */

  Literal* l1 = ~(p(3 *     4 )); 
  /*                ^^^^^^^^^ will be interpretd as num(3*4) ==> num(12) */
  Literal* l2 = ~(p(3 * num(4))); 
  /*                ^^^^^^^^^ will be interpretd as num(3)*num(4) */
  Literal* l3 = ~(p(12 )); 

  ASS_NEQ(l1, l2);
  ASS_EQ(l1, l3);
}


TEST_FUN(get_functors) {
  THEORY_SYNTAX_SUGAR(RAT) /* <-- imports syntax sugar */
  THEORY_SYNTAX_SUGAR_FUN  (fn,   2) /* <-- creates an uninterpreted  function over the rational sort with arity 2 */
  THEORY_SYNTAX_SUGAR_PRED (pred, 1) /* <-- creates an uninterpreted predicate over the rational sort with arity 1 */
  THEORY_SYNTAX_SUGAR_CONST(cons   ) /* <-- creates an uninterpreted  constant */

  /* we can query the functors of functionsm, constants and predicates */
  unsigned fnFunctor   = fn.functor(); 
  unsigned consFunctor = cons.functor(); 
  unsigned predFunctor = pred.functor(); 

  perform_test(
      fnFunctor,
      consFunctor,
      predFunctor
  );
}

TEST_FUN(create_equalities) {
  THEORY_SYNTAX_SUGAR(RAT) /* <-- imports syntax sugar */
  THEORY_SYNTAX_SUGAR_FUN  (fn, 2) /* <-- creates an uninterpreted  function over the rational sort with arity 2 */
  THEORY_SYNTAX_SUGAR_CONST(cons ) /* <-- creates an uninterpreted  constant */

  Literal* l1 = fn(cons, x) == y;
  Literal* l2 = fn(cons, x) != y;

  perform_test(l1, l2);
}


TEST_FUN(create_unitnterpreted) {
  FOF_SYNTAX_SUGAR             /* <-- imports syntax sugar for an uninterpreted sort alpha */
  FOF_SYNTAX_SUGAR_FUN  (f, 2) /* <-- creates an uninterpreted  function over the unitererpreted sort alpha with arity 2 */
  FOF_SYNTAX_SUGAR_PRED (p, 1) /* <-- creates an uninterpreted predicate over the unitererpreted sort alpha with arity 2 */
  FOF_SYNTAX_SUGAR_CONST(c)    /* <-- creates an uninterpreted  constant of sort alpha*/

  Literal* l1 = f(c, x) == y;
  Literal* l2 = p(z);

  perform_test(l1, l2);
}
