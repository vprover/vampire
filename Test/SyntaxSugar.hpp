
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
#include "Kernel/NumTraits.hpp"

#include "Indexing/TermSharing.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Sorts.hpp"

#define __CLSR_RELATION(name, inter)                                                                                    \
  auto name = [](TermWrapper lhs, TermWrapper rhs) -> Literal&  {                                                       \
    return *Literal::create2(env.signature->getInterpretingSymbol(inter),  true, lhs,rhs);                              \
  };                                                                                                                    \
 
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

#define __CLSR_FUN_INTERPRETED(arity, mul, INT, _MULTIPLY)                                                              \
    auto mul = [](__ARGS_DECL(TermWrapper, arity)) -> TermWrapper {                                                     \
      return TermList(Term::create ## arity(                                                                            \
            env.signature->getInterpretingSymbol(Theory::Interpretation:: INT ## _MULTIPLY),                            \
            __ARGS_EXPR(Type, arity))                                                                                   \
          );                                                                                                            \
    };                                                                                                                  \

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

#define __DECLARE_CONST(      f, sort) ConstSugar<decltype(sort)                                 > f(#f, sort);
#define __DECLARE_FUNC(arity, f, sort)  FuncSugar<decltype(sort), __REPEAT(arity, decltype(sort))> f(#f, sort, __REPEAT(arity, sort));
#define __DECLARE_PRED(arity, f, sort)  PredSugar<                __REPEAT(arity, decltype(sort))> f(#f,       __REPEAT(arity, sort));

#define __DEFAULT_VARS                                                                                                  \
    auto x = TermWrapper(TermList::var(0));                                                                             \
    auto y = TermWrapper(TermList::var(1));                                                                             \
    auto z = TermWrapper(TermList::var(2));                                                                             \


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
 * to terms in the corresponding sort, and operators to build complex terms and literals. Further it sets 
 * some (C++) variables to variable terms and some to constant terms.
 *
 * Additionally the macros `THEORY_SYNTAX_SUGAR_FUN`, `THEORY_SYNTAX_SUGAR_CONST`, and `THEORY_SYNTAX_SUGAR_PRED` can be 
 * used to declare uninterpreted functions/predicates/constants over the sort.
 *
 * These are the automatically defined operators and variables
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
 * Operators for creating complex terms:
 * operator* ... interpreted multiplication
 * operator+ ... interpreted addition
 * operator- ... interpreted unary minus
 *
 * Operators for creating literals:
 * operator>   ... interpreted greater relation
 * operator>=  ... interpreted greater or equal relation
 * operator<   ... interpreted less relation
 * operator<=  ... interpreted less or equal relation
 * operator==  ... interpreted equality relation
 * operator!=  ... interpreted equality relation
 * operator~   ... flipping a literal's polarity
 *
 * Other closures:
 * frac(int,int) ... creates a fractional interpreted constant (only for REAL, and RAT)
 * num(int)      ... explicity converts a number to an interpreted constant 
 *                   this can be needed in order to prevent the compiler from pre-evaluating integer expressions.
 *                   e.g. {
 *                      Literal* l1 = (a == (3 * 2));
 *                                          ^^^^^^^ this will be evaluated to 6 before transforming it into a term
 *                                                  in order to prevent this we can write:
 *                      Literal* l2 = (a == (num(3) * 2));
 *                   }
 *
 * For examples see UnitTesting/tSyntaxSugar.cpp.
 */
#define THEORY_SYNTAX_SUGAR(sort)                                                                                       \
  _Pragma("GCC diagnostic push")                                                                                        \
  _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                                        \
    using DefaultSort = NumTraits<__CONSTANT_TYPE_ ## sort>;                                                            \
    using TermWrapper = Trm<DefaultSort>;                                                                               \
    DefaultSort __defaultSort;                                                                                          \
                                                                                                                        \
    __DEFAULT_VARS                                                                                                      \
    __DECLARE_CONST(a, __defaultSort)                                                                                   \
    __DECLARE_CONST(b, __defaultSort)                                                                                   \
    __DECLARE_CONST(c, __defaultSort)                                                                                   \
      auto num = [](int n) -> TermWrapper {  return n; };                                                               \
    __IF_FRAC(sort,                                                                                                     \
      auto frac = [](int num, int den) -> TermWrapper {                                                                 \
        return DefaultSort::constantTl(num, den);                                                                       \
      };                                                                                                                \
    )                                                                                                                   \
    __CLSR_FUN_INTERPRETED(2, mul, sort, _MULTIPLY)                                                                     \
    __CLSR_FUN_INTERPRETED(1, minus, sort, _UNARY_MINUS)                                                                \
  _Pragma("GCC diagnostic pop")                                                                                         \

#define THEORY_SYNTAX_SUGAR_FUN(f, arity)  __DECLARE_FUNC(arity, f, __defaultSort)
#define THEORY_SYNTAX_SUGAR_PRED(f, arity) __DECLARE_PRED(arity, f, __defaultSort)
#define THEORY_SYNTAX_SUGAR_CONST(f)       __DECLARE_CONST(      f, __defaultSort)

#define FOF_SYNTAX_SUGAR                                                                                                \
  _Pragma("GCC diagnostic push")                                                                                        \
  _Pragma("GCC diagnostic ignored \"-Wunused\"")                                                                        \
    using DefaultSort = UninterpretedTraits;                                                                            \
    using TermWrapper = Trm<DefaultSort>;                                                                               \
    DefaultSort __defaultSort(env.sorts->addSort("alpha", false));                                                      \
    __DEFAULT_VARS                                                                                                      \
  _Pragma("GCC diagnostic pop")                                                                                         \

#define FOF_SYNTAX_SUGAR_PRED(f, arity) __DECLARE_PRED(arity, f, __defaultSort)
#define FOF_SYNTAX_SUGAR_FUN(f, arity)  __DECLARE_FUNC(arity, f, __defaultSort)
#define FOF_SYNTAX_SUGAR_CONST(f)       __DECLARE_CONST(      f, __defaultSort)

#define __IF_FRAC(sort, ...) __IF_FRAC_##sort(__VA_ARGS__)
#define __IF_FRAC_INT(...)
#define __IF_FRAC_RAT(...) __VA_ARGS__
#define __IF_FRAC_REAL(...) __VA_ARGS__

struct UninterpretedTraits 
{
  unsigned _srtNumber;

public:
  UninterpretedTraits(unsigned srtNumber) : _srtNumber(srtNumber) {}
  unsigned sortNumber() const { return _srtNumber; }
};

template<class SortTraits>
class Trm 
{
  TermList _trm;

public:
  /* works only if SortTraits is a NumTraits specialization */
  Trm(int trm) 
    : _trm(SortTraits::constantTl(trm)) {  }

  Trm(TermList trm) 
    : _trm(trm)
  { ASS_REP(!_trm.isEmpty(), _trm);  }

  /** implicit conversion */ 
  operator TermList() const {return _trm;}

  /** explicit conversion */ 
  TermList toTerm() const { return _trm;} 

  static Trm createConstant(const char* name, SortTraits s) {
    unsigned f = env.signature->addFunction(name,0);                                                                
    env.signature->getFunction(f)->setType(OperatorType::getFunctionType({}, s.sortNumber())); 
    return Trm(TermList(Term::createConstant(f)));                                                          
  }                                                                                                                 

  static Trm createConstant(const char* name) {
    return createConstant(name, SortTraits{});
  }                                                                                                                 
};

class Lit
{
  Literal* _lit;
public:
  Lit(Literal* lit) : _lit(lit) {}
  operator Literal*() const { return _lit; }
};

////////////////////////// operators to create terms ////////////////////////// 

template<class Number> Trm<Number> operator+(Trm<Number> lhs, Trm<Number> rhs)  { return Number::add(lhs, rhs); }  
template<class Number> Trm<Number> operator*(Trm<Number> lhs, Trm<Number> rhs)  { return Number::mul(lhs, rhs); }  
template<class Number> Trm<Number> operator/(Trm<Number> lhs, Trm<Number> rhs)  { return Number::div(lhs, rhs); }  

#define __IMPL_NUMBER_BIN_FUN(op, result_t)                                                                            \
  template<class Number> result_t op(int lhs, Trm<Number> rhs) { return op(Trm<Number>(lhs), rhs); }             \
  template<class Number> result_t op(Trm<Number> lhs, int rhs) { return op(lhs, Trm<Number>(rhs)); }             \

__IMPL_NUMBER_BIN_FUN(operator+, Trm<Number>)
__IMPL_NUMBER_BIN_FUN(operator*, Trm<Number>)
__IMPL_NUMBER_BIN_FUN(operator/, Trm<Number>)

#define __BIN_FUNC_QUOTIENT_REMAINDER(X) \
  template<class Number> \
  Trm<Number>  quotient##X(Trm<Number> lhs, Trm<Number> rhs){ return Number:: quotient##X(lhs, rhs); }   \
  \
  template<class Number> \
  Trm<Number> remainder##X(Trm<Number> lhs, Trm<Number> rhs){ return Number::remainder##X(lhs, rhs); }   \
  \
  __IMPL_NUMBER_BIN_FUN( quotient##X, Trm<Number>) \
  __IMPL_NUMBER_BIN_FUN(remainder##X, Trm<Number>) \

__BIN_FUNC_QUOTIENT_REMAINDER(E)
__BIN_FUNC_QUOTIENT_REMAINDER(T)
__BIN_FUNC_QUOTIENT_REMAINDER(F)

#undef __BIN_FUNC_QUOTIENT_REMAINDER


template<class Number> 
Trm<Number> operator-(Trm<Number> x) 
{
  return Number::minus(x);
}

////////////////////////// operators to create literals ////////////////////////// 

template<class Sort> 
Lit operator==(Trm<Sort> lhs, Trm<Sort> rhs) 
{
  unsigned sort;
  ALWAYS(SortHelper::tryGetResultSort(lhs, sort) || SortHelper::tryGetResultSort(rhs, sort));
  return Literal::createEquality(true, lhs, rhs, sort);
}


template<class Number> Lit operator< (Trm<Number> lhs, Trm<Number> rhs) { return Number::less   (true, lhs, rhs); }
template<class Number> Lit operator<=(Trm<Number> lhs, Trm<Number> rhs) { return Number::leq    (true, lhs, rhs); }
template<class Number> Lit operator> (Trm<Number> lhs, Trm<Number> rhs) { return Number::greater(true, lhs, rhs); }
template<class Number> Lit operator>=(Trm<Number> lhs, Trm<Number> rhs) { return Number::geq    (true, lhs, rhs); }

inline Lit operator~(Lit lit) 
{
  Literal* l = lit;
  return Literal::create(l, !l->polarity());
}

template<class Sort> 
Lit operator!=(Trm<Sort> lhs, Trm<Sort> rhs) 
{
  return ~(lhs == rhs);
}

__IMPL_NUMBER_BIN_FUN(operator==, Lit)
__IMPL_NUMBER_BIN_FUN(operator!=, Lit)
__IMPL_NUMBER_BIN_FUN(operator< , Lit)
__IMPL_NUMBER_BIN_FUN(operator<=, Lit)
__IMPL_NUMBER_BIN_FUN(operator> , Lit)
__IMPL_NUMBER_BIN_FUN(operator>=, Lit)


template<class ResultSort, class... ArgSorts>
class FuncSugar {
  unsigned _functor;

public:
  FuncSugar(const char* name, ResultSort r, ArgSorts... args) 
  {
    BYPASSING_ALLOCATOR
    std::vector<unsigned> as = { args.sortNumber()... };
    _functor = env.signature->addFunction(name, as.size());
    env.signature
      ->getFunction(_functor)
      ->setType(OperatorType::getFunctionType(as.size(), &as[0], r.sortNumber()));    
  }

  Trm<ResultSort> operator()(Trm<ArgSorts>... args) const {
    BYPASSING_ALLOCATOR
    std::vector<TermList> as = { Trm<ArgSorts>(args).toTerm()... };
    return TermList(Term::create(_functor, 
        as.size(), 
        &as[0] ));
  }
  unsigned functor() const { return _functor; }
};

template<class SortTraits>
class ConstSugar : public Trm<SortTraits> 
{
public:
  ConstSugar(const char* name, SortTraits s) 
    : Trm<SortTraits>(Trm<SortTraits>::createConstant(name, s).toTerm()) 
  { }
  unsigned functor() const { return this->toTerm().term()->functor(); }
};

template<class... ArgSorts>
class PredSugar {
  unsigned _functor;

public:
  PredSugar(const char* name, ArgSorts... args) 
  {
    BYPASSING_ALLOCATOR
    std::vector<unsigned> as = { args.sortNumber()... };
    _functor = env.signature->addPredicate(name, as.size());
    env.signature
      ->getPredicate(_functor)
      ->setType(OperatorType::getPredicateType(as.size(), &as[0]));    
  }

  Lit operator()(Trm<ArgSorts>... args) const {
    BYPASSING_ALLOCATOR
    std::vector<TermList> as = { Trm<ArgSorts>(args).toTerm()... };
    return Literal::create(_functor, 
        as.size(), 
        /* polarity */ true, 
        /* commutative */ false, 
        &as[0] );
  }
  unsigned functor() const { return _functor; }
};


inline Clause& clause(std::initializer_list<Literal*> ls) { 
  static Inference testInf = Kernel::NonspecificInference0(UnitInputType::ASSUMPTION, InferenceRule::INPUT); 
  Clause& out = *new(ls.size()) Clause(ls.size(), testInf); 
  auto l = ls.begin(); 
  for (int i = 0; i < ls.size(); i++) { 
    out[i] = *l; 
    l++; 
  }
  return out; 
}

#endif // __TEST__SYNTAX_SUGAR__H__
