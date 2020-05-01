/**! This file contains macros to provide syntax sugar for building formulas,
 * terms, etc. for test cases.
 *
 * Macros that are not meant to be used from outside of this file are prefixed 
 * with two underscores.
 *
 * @autor Johannes Schoisswohl
 * @date 2020-04-29
 */

#ifndef __TEST__SYNTAX_SUGAR__H__
#define __TEST__SYNTAX_SUGAR__H__

#include "Forwards.hpp"
#include "Lib/Environment.hpp"

#include "Indexing/TermSharing.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"

#define __CLSR_RELATION(name, inter) \
  auto name = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  {  \
    return *Literal::create2(env.signature->addInterpretedPredicate(inter, #name),  \
        true, lhs,rhs);  \
  }; \
 
 
#define __FROM_FRAC_INT 
#define __FROM_FRAC_REAL \
  auto frac = [](int a, int b) -> TermWrapper {   \
    return TermList(theory->representConstant(RealConstantType(RationalConstantType(a,b)))); \
  }; 
#define __FROM_FRAC_RAT \
  auto frac = [](int a, int b) -> TermWrapper {   \
    return TermList(theory->representConstant(RationalConstantType(a,b))); \
  }; 

#define __TO_SORT_RAT Sorts::SRT_RATIONAL
#define __TO_SORT_INT Sorts::SRT_INTEGER
#define __TO_SORT_REAL Sorts::SRT_REAL

#define __CONSTANT_TYPE_INT  IntegerConstantType
#define __CONSTANT_TYPE_REAL RealConstantType
#define __CONSTANT_TYPE_RAT  RationalConstantType
 
#define __ARGS_DECL(Type, arity) __ARGS_DECL_ ## arity(Type)
#define __ARGS_DECL_1(Type) Type arg0_ 
#define __ARGS_DECL_2(Type) Type arg0_ , Type arg1_ 

#define __ARGS_EXPR(Type, arity) __ARGS_EXPR_ ## arity(Type)
#define __ARGS_EXPR_1(Type) arg0_
#define __ARGS_EXPR_2(Type) arg0_, arg1_

#define __CLSR_FUN_INTERPRETED(arity, mul, INT, _MULTIPLY) \
    auto mul = [](__ARGS_DECL(TermWrapper, arity)) -> TermWrapper {  \
      return TermList(Term::create ## arity( \
            env.signature->addInterpretedFunction(Theory::Interpretation:: INT ## _MULTIPLY, #mul),\
            __ARGS_EXPR(Type, arity))\
          );\
    }; \

#define __CLSR_FUN_UNINTERPRETED(f, sort) \
  auto f = [](TermWrapper args) -> TermWrapper  {  \
    unsigned f = env.signature->addFunction("f",1);  \
    static bool set = false;  \
    if (!set) {  \
      env.signature->getFunction(f)->setType(OperatorType::getFunctionType({ sort }, sort));  \
      set = true;  \
    }  \
    return TermList(Term::create1(f, args));  \
  };  \

#define __CLSR_CONS_UNINTERPRETED(name, sort) \
  TermWrapper name = 0;\
  { \
    unsigned f = env.signature->addFunction(#name,0);  \
    static bool set = false;  \
    if (!set) {  \
      env.signature->getFunction(f)->setType(OperatorType::getFunctionType({},sort));  \
      set = true;  \
    }  \
    name = TermWrapper(TermList(Term::createConstant(f)));  \
  }  \

/** tldr: For examples on usage see UnitTesting/tSyntaxSugar.cpp
 *
 * This macro provides syntax sugar for building terms and clauses in a one-sorted theory of numbers. 
 *
 * i.e. the theories supported are:
 * THEORY_SYNTAX_SUGAR(INT) ==> integer arithmetic 
 * THEORY_SYNTAX_SUGAR(RAT) ==> rational arithmetic 
 * THEORY_SYNTAX_SUGAR(REAL) ==> rational arithmetic 
 *
 * The macro is meant to be called within a TEST_FUN(...){...} block to import the syntax sugar for 
 * the corresponding test case. It provides a class TermWrapper that implicitly converts number literals 
 * to terms in the corresponding sort, and closures to build complex terms. Further it sets some C++ variables 
 * to variable terms and some to constant terms.
 *
 * local variables:
 * x ... variable X0
 * y ... variable X1
 * z ... variable X2
 *
 * a ... constant a
 * b ... constant b
 * c ... constant c
 *
 * Closures for complex terms:
 * mul   ... interpreted multiplication
 * add   ... interpreted addition
 * minus ... interpreted unary minus
 * f     ... uninterpreted function with arity 1
 *
 * Closures for literals:
 * gt   ... interpreted greater relation
 * geq  ... interpreted greater or equal relation
 * lt   ... interpreted less relation
 * leq  ... interpreted less or equal relation
 * eq   ... interpreted equality relation
 * neq  ... interpreted equality relation
 *
 * Other closures:
 * frac(int,int) ... creates a fractional interpreted constant (only for REAL, and RAT)
 * neg(Literal)  ... negates a literal
 *
 *
 * For examples ses:
 *
 * TEST_FUN(some_meaningful_testname) {
 *   THEORY_SYNTAX_SUGAR(REAL)
 *   Literal& lit = neq(lt(0, mul(x, frac(7,1))));
 *   ... some tests with this literal ...
 * }
 *
 * TEST_FUN(some_other_meaningful_testname) {
 *   THEORY_SYNTAX_SUGAR(REAL)
 *   TermList lit = mul(x, frac(7,1));
 *   ... some tests with this literal ...
 * }
 */
#define THEORY_SYNTAX_SUGAR(sort)  \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wunused\"") \
    \
    class TermWrapper { \
      TermList _term; \
    public: \
      TermWrapper(int i) : TermWrapper(TermList(theory->representConstant(__CONSTANT_TYPE_ ## sort (i)))) { \
        ASS_REP(!_term.isEmpty(), _term); \
      }; \
      TermWrapper(TermList t) : _term(t) { \
        ASS_REP(!_term.isEmpty(), _term); \
      } \
      operator TermList() {return _term;} \
    }; \
   \
    auto eq = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  { return *Literal::createEquality(true, lhs, rhs, __TO_SORT_ ## sort); };  \
    auto neq = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  { return *Literal::createEquality(false, lhs, rhs, __TO_SORT_ ## sort); };  \
    auto neg = [](Literal& l) -> Literal&  {  \
      return *Literal::create(&l, !l.polarity()); \
    };  \
    auto x = TermWrapper(TermList::var(0));\
    auto y = TermWrapper(TermList::var(1));\
    auto z = TermWrapper(TermList::var(2));\
    __CLSR_CONS_UNINTERPRETED(a, __TO_SORT_ ## sort) \
    __CLSR_CONS_UNINTERPRETED(b, __TO_SORT_ ## sort) \
    __CLSR_CONS_UNINTERPRETED(c, __TO_SORT_ ## sort) \
    __IF_FRAC(sort, __CLSR_FUN_INTERPRETED(2, div, sort, _QUOTIENT)) \
    __CLSR_FUN_INTERPRETED(2, mul, sort, _MULTIPLY) \
    __CLSR_FUN_INTERPRETED(2, add, sort, _PLUS) \
    __CLSR_FUN_INTERPRETED(1, minus, sort, _UNARY_MINUS) \
    __CLSR_FUN_UNINTERPRETED(f, __TO_SORT_ ## sort) \
    __FROM_FRAC_ ## sort \
    __CLSR_RELATION(gt, Theory::Interpretation::sort ## _GREATER)\
    __CLSR_RELATION(geq, Theory::Interpretation::sort ## _GREATER_EQUAL)\
    __CLSR_RELATION(lt, Theory::Interpretation::sort ## _LESS)\
    __CLSR_RELATION(leq, Theory::Interpretation::sort ## _LESS_EQUAL)\
  _Pragma("GCC diagnostic pop") \

#define __IF_FRAC(sort, ...) __IF_FRAC_##sort(__VA_ARGS__)
#define __IF_FRAC_INT(...)
#define __IF_FRAC_RAT(...) __VA_ARGS__
#define __IF_FRAC_REAL(...) __VA_ARGS__

#endif // __TEST__SYNTAX_SUGAR__H__
