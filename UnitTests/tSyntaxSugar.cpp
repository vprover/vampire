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

template<class... A>
void perform_test(const A&...) 
{ /* dummy function to get rid of warnings */ }

TEST_FUN(some_meaningful_testname) {
  
  NUMBER_SUGAR(Real) // <- imports syntax sugar for +, *, /, and other 
                     //    intepreted functions & predicates on reals

  DECL_DEFAULT_VARS  // <- creates variables x ... variable X0
                     //                      y ... variable X1
                     //                      z ... variable X2

  Literal* lit = ~(0 < (x * frac(7,2)));
  //                        ^^^^^^^^^ creates the numeral 7 / 2

  perform_test(lit);
}

TEST_FUN(some_other_meaningful_testname) {
  NUMBER_SUGAR(Rat)
  DECL_DEFAULT_VARS

  TermList t = x * frac(7,3);

  perform_test(t);
}


TEST_FUN(uninterpreted_and_interpreted_stuff) {
  NUMBER_SUGAR(Rat)                
  DECL_DEFAULT_VARS

  DECL_SORT(alpha)     // <- creates an uninterpred sort 
  DECL_CONST(a, alpha) // <- creates an constant of sort alpha
  DECL_FUNC(fn      , {Rat,alpha}, Rat) // creates an uninterpreted function  f : Rat x alpha -> Rat
  DECL_PRED(relation, {Rat,Rat})        // creates an uninterpreted predicate p : P(Rat x Rat)


  Literal* t = relation(x, fn(frac(7,3), a));

  perform_test(t);
}

TEST_FUN(only_uninterpreted_stuff) {
  DECL_DEFAULT_VARS /* <-- declares variables x (= X0), y (= X1), z (= X2) */

  DECL_SORT(alpha)  /* <- declares a sort */
  DECL_SORT(beta)   /* <- declares another sort */

  DECL_FUNC(f, {beta, beta}, alpha); /* <- declares a function f : alpha x alpha -> beta */
  DECL_CONST(a, alpha); /* <- declares a function f : alpha x alpha -> beta */
  DECL_CONST(b, beta);  /* <- declares a function f : alpha x alpha -> beta */

  perform_test(f(b,b) == a);
}


TEST_FUN(watch_out_for_this) {
  NUMBER_SUGAR(Real)
  DECL_PRED(p, {Real}) 

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
  NUMBER_SUGAR(Rat)                 
  DECL_FUNC( fn  , {Rat, Rat}, Rat)
  DECL_PRED( pred, {Rat})          
  DECL_CONST(cons, Rat)           

  // we can query the functors of functionsm, constants and predicates 
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
  NUMBER_SUGAR(Rat)
  DECL_DEFAULT_VARS
  DECL_FUNC(fn, {Rat, Rat}, Rat)
  DECL_CONST(cons, Rat)

  // we can creat equality literals
  Literal* l1 = fn(cons, x) == y;
  Literal* l2 = fn(cons, x) != y;

  perform_test(l1, l2);
}

TEST_FUN(term_algebra) {
  DECL_DEFAULT_VARS 

  DECL_SORT(alpha)
  DECL_SORT(list)  
 
  DECL_CONST(a, alpha)  
  DECL_PRED(p, {list})  

  // creating a term algebra:
  // declare constructors first
  DECL_CONST(nil               , list)
  DECL_FUNC(cons, {alpha, list}, list)

  // then turn them into a term algebra
  DECL_TERM_ALGEBRA(list, {nil, cons})
  
  perform_test(p(cons(a,nil)));
}
