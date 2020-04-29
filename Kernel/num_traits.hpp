#ifndef __NUM_TRAITS_H__
#define __NUM_TRAITS_H__
#include "Term.hpp"
#include "Theory.hpp"

namespace Kernel {

//TODO document
template<class A>
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
  constexpr CamelCase ## ConstantType num_traits<CamelCase ## ConstantType>::one;\
  constexpr CamelCase ## ConstantType num_traits<CamelCase ## ConstantType>::zero;\

IMPL_NUM_TRAITS(Rational, RATIONAL, RAT )
IMPL_NUM_TRAITS(Real    , REAL    , REAL)
IMPL_NUM_TRAITS(Integer , INTEGER , INT )


}
#endif // __NUM_TRAITS_H__
