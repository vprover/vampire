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
#include "Kernel/Inference.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/SortHelper.hpp"

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
#define __ARGS_DECL_2(Type) __ARGS_DECL_1(Type) , Type arg1_ 
#define __ARGS_DECL_3(Type) __ARGS_DECL_2(Type) , Type arg2_ 
#define __ARGS_DECL_4(Type) __ARGS_DECL_3(Type) , Type arg3_ 
#define __ARGS_DECL_5(Type) __ARGS_DECL_4(Type) , Type arg4_ 
#define __ARGS_DECL_6(Type) __ARGS_DECL_5(Type) , Type arg5_ 
#define __ARGS_DECL_7(Type) __ARGS_DECL_6(Type) , Type arg6_ 
#define __ARGS_DECL_8(Type) __ARGS_DECL_7(Type) , Type arg7_ 
#define __ARGS_DECL_9(Type) __ARGS_DECL_8(Type) , Type arg8_ 
#define __ARGS_DECL_10(Type) __ARGS_DECL_9(Type) , Type arg9_ 

#define __ARGS_EXPR(Type, arity) __ARGS_EXPR_ ## arity(Type)
#define __ARGS_EXPR_1(Type) arg0_
#define __ARGS_EXPR_2(Type) __ARGS_EXPR_1(Type), arg1_
#define __ARGS_EXPR_3(Type) __ARGS_EXPR_2(Type), arg2_
#define __ARGS_EXPR_4(Type) __ARGS_EXPR_3(Type), arg3_
#define __ARGS_EXPR_5(Type) __ARGS_EXPR_4(Type), arg4_
#define __ARGS_EXPR_6(Type) __ARGS_EXPR_5(Type), arg5_
#define __ARGS_EXPR_7(Type) __ARGS_EXPR_6(Type), arg6_
#define __ARGS_EXPR_8(Type) __ARGS_EXPR_7(Type), arg7_
#define __ARGS_EXPR_9(Type) __ARGS_EXPR_8(Type), arg8_
#define __ARGS_EXPR_10(Type) __ARGS_EXPR_9(Type), arg9_

#define __REPEAT_1(sort) sort
#define __REPEAT_2(sort) sort, __REPEAT_1(sort)
#define __REPEAT_3(sort) sort, __REPEAT_2(sort)
#define __REPEAT_4(sort) sort, __REPEAT_3(sort)
#define __REPEAT_5(sort) sort, __REPEAT_4(sort)
#define __REPEAT_6(sort) sort, __REPEAT_5(sort)
#define __REPEAT_7(sort) sort, __REPEAT_6(sort)
#define __REPEAT_8(sort) sort, __REPEAT_7(sort)
#define __REPEAT_9(sort) sort, __REPEAT_8(sort)
#define __REPEAT_10(sort) sort, __REPEAT_9(sort)
#define __REPEAT(arity, sort) __REPEAT_ ## arity(sort)

#define __CLSR_FUN(n_args, f, funct) \
  class __ ##  f ## __CLASS { \
    unsigned _functor;\
  public:\
    __ ##  f ## __CLASS(unsigned functor)  \
     : _functor(functor) { \
    }\
    TermWrapper operator()(__ARGS_DECL(TermWrapper, n_args)) {  \
      return TermList(Term::create(_functor, {__ARGS_EXPR(TermWrapper, n_args)}));  \
    };  \
    unsigned functor() const { return _functor; } \
  };\
  auto f = __ ##  f ## __CLASS(funct);


#define __CLSR_FUN_NUMBER(arity, mul, INT, _MULTIPLY) \
   __CLSR_FUN(arity, mul,  \
       env.signature->addInterpretedFunction(Theory::Interpretation:: INT ## _MULTIPLY, #mul)) \

#define __CLSR_FUN_UNINTERPRETED(n_args, f, ...) \
  env.signature->getFunction(env.signature->addFunction(#f, n_args))  \
               ->setType(OperatorType::getFunctionType(__VA_ARGS__)); \
  __CLSR_FUN(n_args, f, \
      env.signature->getFunctionNumber(#f, n_args))

#define __CLSR_PRED_UNINTERPRETED(arity, p, sort) \
  auto p = [&](__ARGS_DECL(TermWrapper, arity)) -> Literal&  {  \
    unsigned p = env.signature->addPredicate(#p, arity);  \
    static bool set = false;  \
    if (!set) {  \
      env.signature->getPredicate(p)->setType(OperatorType::getPredicateType({ __REPEAT(arity, sort) }));  \
      set = true;  \
    }  \
    return *Literal::create(p, true, {__ARGS_EXPR(TermWrapper, arity)}); \
  };  \

#define __CLSR_CONST_UNINTERPRETED(name, sort) \
  class __ ## name ## __CLASS { \
    TermWrapper _self; \
    public: \
    __ ## name ## __CLASS(const char* name, unsigned s)   \
      : _self( TermWrapper::createConstant(#name, s) ) \
    { } \
    \
    operator TermList() { return _self; } \
    operator TermWrapper() { return _self; } \
    unsigned functor() { return _self.toTerm().term()->functor(); } \
  }; \
  auto name = __ ## name ## __CLASS(#name, sort);

#define __TERM_WRAPPER_CLASS(...) \
    class TermWrapper { \
      TermList _term; \
    public: \
      TermWrapper(TermList t) : _term(t) { \
        ASS_REP(!_term.isEmpty(), _term); \
      } \
      operator TermList() {return _term;} \
      TermList toTerm() {return _term;} \
      static TermWrapper createConstant(const char* name, unsigned sort) { \
        unsigned f = env.signature->addFunction(name,0);  \
        env.signature->getFunction(f)->setType(OperatorType::getFunctionType({},sort));  \
        return TermWrapper(TermList(Term::createConstant(f)));  \
      } \
      __VA_ARGS__ \
    }; \

#define __DEFAULT_VARS \
    auto x = TermWrapper(TermList::var(0));\
    auto y = TermWrapper(TermList::var(1));\
    auto z = TermWrapper(TermList::var(2));\


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
    auto __default_sort = __TO_SORT_ ## sort; \
    auto sort = __TO_SORT_ ## sort; \
    \
    __TERM_WRAPPER_CLASS( \
      TermWrapper(int i) : TermWrapper(TermList(theory->representConstant(__CONSTANT_TYPE_ ## sort (i)))) { \
        ASS_REP(!_term.isEmpty(), _term); \
      }; \
    )\
      \
    auto eq = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  {  \
      unsigned srt; \
      ALWAYS(SortHelper::tryGetResultSort(lhs, srt)  \
          || SortHelper::tryGetResultSort(rhs, srt)); \
      return *Literal::createEquality(true, lhs, rhs, srt);  \
    };   \
\
    auto neg = [](Literal& l) -> Literal&  {  \
      return *Literal::create(&l, !l.polarity()); \
    };  \
    auto neq = [&](TermWrapper lhs, TermWrapper rhs) -> Literal&  { \
      return neg(eq(lhs,rhs)); \
    };  \
    __DEFAULT_VARS \
    __CLSR_CONST_UNINTERPRETED(a, __TO_SORT_ ## sort) \
    __CLSR_CONST_UNINTERPRETED(b, __TO_SORT_ ## sort) \
    __CLSR_CONST_UNINTERPRETED(c, __TO_SORT_ ## sort) \
    __IF_FRAC(sort, __CLSR_FUN_NUMBER(2, div, sort, _QUOTIENT)) \
    __CLSR_FUN_NUMBER(2, mul, sort, _MULTIPLY) \
    __CLSR_FUN_NUMBER(2, add, sort, _PLUS) \
    __CLSR_FUN_NUMBER(1, minus, sort, _UNARY_MINUS) \
    __FROM_FRAC_ ## sort \
    __CLSR_RELATION(gt, Theory::Interpretation::sort ## _GREATER)\
    __CLSR_RELATION(geq, Theory::Interpretation::sort ## _GREATER_EQUAL)\
    __CLSR_RELATION(lt, Theory::Interpretation::sort ## _LESS)\
    __CLSR_RELATION(leq, Theory::Interpretation::sort ## _LESS_EQUAL)\
  _Pragma("GCC diagnostic pop") \

////////////////////

#define ARRAY_SYNTAX_SUGAR(arraySrt, idx, cont) \
    auto arraySrt = env.sorts->addArraySort(idx, cont); \
    __CLSR_FUN(3, store, env.signature->getInterpretingSymbol( \
          Theory::Interpretation::ARRAY_STORE, \
          OperatorType::getFunctionType({arraySrt, idx, cont}, arraySrt)) \
        ) \
    __CLSR_FUN(2, select, env.signature->getInterpretingSymbol( \
          Theory::Interpretation::ARRAY_SELECT, \
          OperatorType::getFunctionType({arraySrt, idx}, cont)) \
        ) \

#define SYNTAX_SUGAR_SORT(name) \
    auto name = env.sorts->addSort(#name, false); \

#define SYNTAX_SUGAR_CONST(f, srt) \
    __CLSR_CONST_UNINTERPRETED(f, srt)

#define SYNTAX_SUGAR_FUN(f, arity, ...) \
    __CLSR_FUN_UNINTERPRETED(arity, f, __VA_ARGS__)

////////////////////

#define THEORY_SYNTAX_SUGAR_CONST(f) \
    __CLSR_CONST_UNINTERPRETED(f, __default_sort)

#define THEORY_SYNTAX_SUGAR_FUN(f, arity) \
    __CLSR_FUN_UNINTERPRETED(arity, f, { __REPEAT(arity, __default_sort) }, __default_sort)

#define THEORY_SYNTAX_SUGAR_PRED(rel, arity) \
    __CLSR_PRED_UNINTERPRETED(arity, rel, __default_sort)

////////////////////

#define FOF_SYNTAX_SUGAR \
  _Pragma("GCC diagnostic push") \
  _Pragma("GCC diagnostic ignored \"-Wunused\"") \
    __TERM_WRAPPER_CLASS() \
    auto __default_sort = env.sorts->addSort("alpha", false); \
    __DEFAULT_VARS \
  _Pragma("GCC diagnostic pop") \

#define FOF_SYNTAX_SUGAR_PRED(f, arity) \
    __CLSR_PRED_UNINTERPRETED(arity, rel, __default_sort)

#define FOF_SYNTAX_SUGAR_FUN(f, arity) \
    __CLSR_FUN_UNINTERPRETED(arity, f, __default_sort)

#define FOF_SYNTAX_SUGAR_CONST(a) \
    __CLSR_CONST_UNINTERPRETED(a, __default_sort) \

#define __IF_FRAC(sort, ...) __IF_FRAC_##sort(__VA_ARGS__)
#define __IF_FRAC_INT(...)
#define __IF_FRAC_RAT(...) __VA_ARGS__
#define __IF_FRAC_REAL(...) __VA_ARGS__

#endif // __TEST__SYNTAX_SUGAR__H__
