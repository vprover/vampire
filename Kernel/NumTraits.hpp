/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __NUM_TRAITS_H__
#define __NUM_TRAITS_H__

#include "Forwards.hpp"
#include "Term.hpp"
#include "Theory.hpp"
#include "Signature.hpp"

namespace Kernel {

/** This struct provides a unified interface to the "number" theories. i.e. these 
 * are the theories of integers, rationals, and reals.
 *
 * For each ConstantType in {IntegerConstantType, RationalConstantType, RealConstantType},
 * there is a specialisation NumTraits<ConstantType> which provides functions for building 
 * terms and literals, accessing the functor/interpretation of some predicate or function. 
 *
 * There are associated constants for the related Sorts::DefaultSorts values, constexpr s 
 * to pattern match on interpretations and special constants (like zero and one), etc.
 *
 * =====
 *
 * To access the functor of some symbol "sym", there is a function 
 * static unsigned symF();
 *
 * e.g.: NumTraits<IntegerConstantType>::lessF()
 *       NumTraits<IntegerConstantType>::addF()
 *
 * =====
 *
 * To access the interpretation of some symbol "sym", there is a constant 
 * static Theory::Interpretation symI;
 *
 * e.g.: NumTraits<IntegerConstantType>::lessI // == Theory::Interpretation INT_LESS;
 *       NumTraits<IntegerConstantType>::addI  // == Theory::Interpretation INT_PLUS;
 *
 * =====
 *
 * To build a term from some function symbol "sym", there is a function
 * static TermList static sym(TermList...);
 *
 * e.g.: NumTraits<IntegerConstantType>::add(lhs, rhs) 
 *
 * =====
 *
 * To build a literal from some predicate symbol "sym", there is a function
 * static Literal* static sym(bool polarity, TermList...);
 *
 * e.g.: NumTraits<IntegerConstantType>::less(true, lhs, rhs) 
 *
 * =====
 *
 * For a special constant cons there is 
 * constexpr static ConstantType consC;
 *
 * e.g.: NumTraits<IntegerConstantType>::zeroC;
 *
 * =====
 *
 * For a complete picture build the doxygen documentaion.
 *
 */
template<class ConstantType>
struct NumTraits;

#define IMPL_NUM_TRAITS__ARG_DECL_1(Type) Type a1
#define IMPL_NUM_TRAITS__ARG_DECL_2(Type) IMPL_NUM_TRAITS__ARG_DECL_1(Type), Type a2
#define IMPL_NUM_TRAITS__ARG_DECL_3(Type) IMPL_NUM_TRAITS__ARG_DECL_2(Type), Type a3
#define IMPL_NUM_TRAITS__ARG_DECL_4(Type) IMPL_NUM_TRAITS__ARG_DECL_3(Type), Type a4
#define IMPL_NUM_TRAITS__ARG_DECL_5(Type) IMPL_NUM_TRAITS__ARG_DECL_4(Type), Type a5
#define IMPL_NUM_TRAITS__ARG_DECL_6(Type) IMPL_NUM_TRAITS__ARG_DECL_5(Type), Type a6
#define IMPL_NUM_TRAITS__ARG_DECL_7(Type) IMPL_NUM_TRAITS__ARG_DECL_6(Type), Type a7
#define IMPL_NUM_TRAITS__ARG_DECL_8(Type) IMPL_NUM_TRAITS__ARG_DECL_7(Type), Type a8
#define IMPL_NUM_TRAITS__ARG_DECL_9(Type) IMPL_NUM_TRAITS__ARG_DECL_8(Type), Type a9
#define IMPL_NUM_TRAITS__ARG_DECL_10(Type) IMPL_NUM_TRAITS__ARG_DECL_9(Type), Type a10

#define IMPL_NUM_TRAITS__ARG_DECL(Type, arity) IMPL_NUM_TRAITS__ARG_DECL_ ## arity (Type)
#define IMPL_NUM_TRAITS__ARG_EXPR(arity) IMPL_NUM_TRAITS__ARG_DECL_ ## arity ()

#define IMPL_NUM_TRAITS__INTERPRETED_SYMBOL(name, SORT_SHORT, _INTERPRETATION)                                \
    static constexpr Theory::Interpretation name ## I = Theory::SORT_SHORT ## _INTERPRETATION;                \
                                                                                                              \
    static unsigned name ## F() {                                                                             \
      static const unsigned functor = env.signature->getInterpretingSymbol(name ## I);                        \
      return functor;                                                                                         \
    }                                                                                                         \


#define IMPL_NUM_TRAITS__INTERPRETED_PRED(name, SORT_SHORT, _INTERPRETATION, arity)                           \
    IMPL_NUM_TRAITS__INTERPRETED_SYMBOL(name, SORT_SHORT, _INTERPRETATION)                                    \
                                                                                                              \
    static Literal* name(bool polarity, IMPL_NUM_TRAITS__ARG_DECL(TermList, arity)) {                         \
      return Literal::create(                                                                                 \
                  name##F(),                                                                                  \
                  polarity,                                                                                   \
                  { IMPL_NUM_TRAITS__ARG_EXPR( arity ) });                                                    \
    }                                                                                                         \



#define IMPL_NUM_TRAITS__INTERPRETED_FUN(name, SORT_SHORT, _INTERPRETATION, arity)                            \
    IMPL_NUM_TRAITS__INTERPRETED_SYMBOL(name, SORT_SHORT, _INTERPRETATION)                                    \
                                                                                                              \
    static TermList name(IMPL_NUM_TRAITS__ARG_DECL(TermList, arity)) {                                        \
      return TermList(                                                                                        \
          Term::create(                                                                                       \
            name##F(),                                                                                        \
            { IMPL_NUM_TRAITS__ARG_EXPR(arity) }));                                                           \
    }                                                                                                         \

#define IMPL_NUM_TRAITS__SPECIAL_CONSTANT(name, value, isName)                                                \
    constexpr static ConstantType name ## C = ConstantType(value);                                            \
    static Term* name ## T() {  /* TODO refactor to const& Term */                                            \
      static Term* trm = theory->representConstant(name ## C);                                                \
      return trm;                                                                                             \
    }                                                                                                         \
    static TermList name()                                                                                    \
    { return TermList(name ## T()); }                                                                         \
                                                                                                              \
    static bool isName(const TermList& l)                                                                     \
    { return l == name(); }                                                                                   \

#define IMPL_NUM_TRAITS__QUOTIENT_REMAINDER(SHORT, X)                                                         \
    IMPL_NUM_TRAITS__INTERPRETED_FUN( quotient ## X, SHORT,  _QUOTIENT_ ## X, 2)                              \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(remainder ## X, SHORT, _REMAINDER_ ## X, 2)                              \
    

#define IMPL_NUM_TRAITS(CamelCase, lowerCase, LONG, SHORT)                                                               \
  template<> struct NumTraits<CamelCase ## ConstantType> {                                                    \
    using ConstantType = CamelCase ## ConstantType;                                                           \
    static TermList sort() { return AtomicSort::lowerCase ## Sort(); };                                              \
                                                                                                              \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(less,    SHORT, _LESS,          2)                                      \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(leq,     SHORT, _LESS_EQUAL,    2)                                      \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(greater, SHORT, _GREATER,       2)                                      \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(geq,     SHORT, _GREATER_EQUAL, 2)                                      \
                                                                                                              \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(isInt,   SHORT, _IS_INT       , 1)                                      \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(isRat,   SHORT, _IS_RAT       , 1)                                      \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(isReal,  SHORT, _IS_REAL      , 1)                                      \
                                                                                                              \
    IMPL_NUM_TRAITS__QUOTIENT_REMAINDER(SHORT, E)                                                             \
    IMPL_NUM_TRAITS__QUOTIENT_REMAINDER(SHORT, T)                                                             \
    IMPL_NUM_TRAITS__QUOTIENT_REMAINDER(SHORT, F)                                                             \
                                                                                                              \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(minus, SHORT, _UNARY_MINUS, 1)                                           \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(add  , SHORT, _PLUS       , 2)                                           \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(mul  , SHORT, _MULTIPLY   , 2)                                           \
    __NUM_TRAITS_IF_FRAC(SHORT,                                                                               \
        IMPL_NUM_TRAITS__INTERPRETED_FUN(div, SHORT, _QUOTIENT, 2)                                            \
        static ConstantType constant(int num, int den) { return ConstantType(num, den); }                     \
        static Term* constantT(int num, int den) { return theory->representConstant(constant(num, den)); }    \
        static TermList constantTl(int num, int den) { return TermList(constantT(num, den)); }                \
    )                                                                                                         \
                                                                                                              \
    IMPL_NUM_TRAITS__SPECIAL_CONSTANT(one , 1, isOne )                                                        \
    IMPL_NUM_TRAITS__SPECIAL_CONSTANT(zero, 0, isZero)                                                        \
                                                                                                              \
    static ConstantType constant(int i) { return ConstantType(i); }                                           \
    static Term* constantT(int i) { return constantT(constant(i)); }                                          \
    static Term* constantT(ConstantType i) { return theory->representConstant(i); }                           \
    static TermList constantTl(int i) { return TermList(constantT(i)); }                                      \
    static Option<ConstantType> tryNumeral(TermList t) {                                                      \
      ConstantType out;                                                                                       \
      if (theory->tryInterpretConstant(t,out)) {                                                              \
        return Option<ConstantType>(out);                                                                     \
      } else {                                                                                                \
        return Option<ConstantType>();                                                                        \
      }                                                                                                       \
    }                                                                                                         \
    static Option<ConstantType> tryNumeral(Term* t) { return tryNumeral(TermList(t)); }                       \
                                                                                                              \
    static const char* name() {return #CamelCase;}                                                            \
  };                                                                                                          \

#define __INSTANTIATE_NUM_TRAITS(CamelCase)                                                                   \
  constexpr CamelCase ## ConstantType NumTraits<CamelCase ## ConstantType>::oneC;                             \
  constexpr CamelCase ## ConstantType NumTraits<CamelCase ## ConstantType>::zeroC;                            \

#define __INSTANTIATE_NUM_TRAITS_ALL                                                                          \
  __INSTANTIATE_NUM_TRAITS(Rational)                                                                          \
  __INSTANTIATE_NUM_TRAITS(Real    )                                                                          \
  __INSTANTIATE_NUM_TRAITS(Integer )                                                                          \

#define __NUM_TRAITS_IF_FRAC(sort, ...) __NUM_TRAITS_IF_FRAC_ ## sort (__VA_ARGS__)
#define __NUM_TRAITS_IF_FRAC_INT(...) 
#define __NUM_TRAITS_IF_FRAC_REAL(...) __VA_ARGS__
#define __NUM_TRAITS_IF_FRAC_RAT(...) __VA_ARGS__

IMPL_NUM_TRAITS(Rational, rational, RATIONAL, RAT )
IMPL_NUM_TRAITS(Real    , real    , REAL    , REAL)
IMPL_NUM_TRAITS(Integer , int     , INTEGER , INT )

#define FOR_NUM_TRAITS(macro)                                                                                 \
  macro(Kernel::NumTraits<Kernel:: IntegerConstantType>)                                                      \
  macro(Kernel::NumTraits<Kernel::    RealConstantType>)                                                      \
  macro(Kernel::NumTraits<Kernel::RationalConstantType>)                                                      \

using IntTraits  = NumTraits< IntegerConstantType>;
using RatTraits  = NumTraits<RationalConstantType>;
using RealTraits = NumTraits<    RealConstantType>;

}
#endif // __NUM_TRAITS_H__
