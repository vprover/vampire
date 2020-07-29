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
  THEORY_SYNTAX_SUGAR(REAL)

  Literal* lit = ~(0 < (x * frac(7,1))); /* <-- imports syntax sugar */

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

