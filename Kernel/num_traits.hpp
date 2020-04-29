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
 * there is a specialisation num_traits<ConstantType> which provides functions for building 
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
 * e.g.: num_traits<IntegerConstantType>::lessF()
 *       num_traits<IntegerConstantType>::addF()
 *
 * =====
 *
 * To access the interpretation of some symbol "sym", there is a constant 
 * static Theory::Interpretation symI;
 *
 * e.g.: num_traits<IntegerConstantType>::lessI // == Theory::Interpretation INT_LESS;
 *       num_traits<IntegerConstantType>::addI  // == Theory::Interpretation INT_PLUS;
 *
 * =====
 *
 * To build a term from some function symbol "sym", there is a function
 * static TermList static sym(TermList...);
 *
 * e.g.: num_traits<IntegerConstantType>::add(lhs, rhs) 
 *
 * =====
 *
 * To build a literal from some predicate symbol "sym", there is a function
 * static Literal* static sym(bool polarity, TermList...);
 *
 * e.g.: num_traits<IntegerConstantType>::less(true, lhs, rhs) 
 *
 * =====
 *
 * For a special constant cons there is 
 * constexpr static ConstantType cons;
 *
 * e.g.: num_traits<IntegerConstantType>::zero;
 *
 * =====
 *
 * For a complete picture build the doxygen documentaion.
 *
 */
template<class ConstantType>
struct num_traits;

#define IMPL_NUM_TRAITS__TERMLIST_ARGS_1 TermList t
#define IMPL_NUM_TRAITS__TERMLIST_EXPR_1          t
#define IMPL_NUM_TRAITS__TERMLIST_ARGS_2 TermList l, TermList r
#define IMPL_NUM_TRAITS__TERMLIST_EXPR_2          l,          r

#define IMPL_NUM_TRAITS__INTERPRETED_SYMBOL(name, SORT_SHORT, _INTERPRETATION) \
    static const Theory::Interpretation name ## I = Theory::SORT_SHORT ## _INTERPRETATION; \
      \
    static unsigned name ## F() { \
      static const unsigned functor = env.signature->getInterpretingSymbol(name ## I);\
      return functor; \
    }\


#define IMPL_NUM_TRAITS__INTERPRETED_PRED(name, SORT_SHORT, _INTERPRETATION, arity) \
    IMPL_NUM_TRAITS__INTERPRETED_SYMBOL(name, SORT_SHORT, _INTERPRETATION) \
                                          \
    static Literal* name(bool polarity, IMPL_NUM_TRAITS__TERMLIST_ARGS_ ## arity) {  \
      return Literal::create( \
                  name##F(),  \
                  polarity, \
                  { IMPL_NUM_TRAITS__TERMLIST_EXPR_ ## arity }); \
    } \



#define IMPL_NUM_TRAITS__INTERPRETED_FUN(name, SORT_SHORT, _INTERPRETATION, arity) \
    IMPL_NUM_TRAITS__INTERPRETED_SYMBOL(name, SORT_SHORT, _INTERPRETATION) \
                                          \
    static TermList name(IMPL_NUM_TRAITS__TERMLIST_ARGS_ ## arity) {  \
      return TermList( \
          Term::create( \
            name##F(),  \
            { IMPL_NUM_TRAITS__TERMLIST_EXPR_ ## arity })); \
    } \

#define IMPL_NUM_TRAITS__SPECIAL_CONSTANT(name, value, isName) \
    constexpr static ConstantType name = ConstantType(value); \
    static Term* name ## T() { \
      static Term* trm = theory->representConstant(name);   \
      return trm; \
    } \
    static bool isName(const TermList& l) { \
      return l.tag() == REF && name ## T() == l.term(); \
    } \

#define IMPL_NUM_TRAITS(CamelCase, LONG, SHORT)  \
  template<> struct num_traits<CamelCase ## ConstantType> { \
    using ConstantType = CamelCase ## ConstantType;                 \
    static const Sorts::DefaultSorts sort = Sorts::SRT_ ## LONG;    \
                                                                    \
    IMPL_NUM_TRAITS__INTERPRETED_PRED(less, SHORT, _LESS, 2) \
                                      \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(minus, SHORT, _UNARY_MINUS, 1) \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(add  , SHORT, _PLUS       , 2) \
    IMPL_NUM_TRAITS__INTERPRETED_FUN(mul  , SHORT, _MULTIPLY   , 2) \
                                                                    \
    IMPL_NUM_TRAITS__SPECIAL_CONSTANT(one , 1, isOne )              \
    IMPL_NUM_TRAITS__SPECIAL_CONSTANT(zero, 0, isZero)              \
  }; \

#define __INSTANTIATE_NUM_TRAITS(CamelCase) \
  constexpr CamelCase ## ConstantType num_traits<CamelCase ## ConstantType>::one;\
  constexpr CamelCase ## ConstantType num_traits<CamelCase ## ConstantType>::zero;\

#define __INSTANTIATE_NUM_TRAITS_ALL \
  __INSTANTIATE_NUM_TRAITS(Rational) \
  __INSTANTIATE_NUM_TRAITS(Real    ) \
  __INSTANTIATE_NUM_TRAITS(Integer ) \


IMPL_NUM_TRAITS(Rational, RATIONAL, RAT )
IMPL_NUM_TRAITS(Real    , REAL    , REAL)
IMPL_NUM_TRAITS(Integer , INTEGER , INT )


}
#endif // __NUM_TRAITS_H__
