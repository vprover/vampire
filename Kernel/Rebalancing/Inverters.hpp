#ifndef __REBALANCING_INVERTERS_H__
#define __REBALANCING_INVERTERS_H__

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include <iostream>

#include "Kernel/num_traits.hpp"

namespace Kernel {
namespace Rebalancing {
namespace Inverters {

template <class C> class NumberTheoryInverter {
  using number = num_traits<C>;

  static bool canInvertTop(Interpretation i, const Term &t, unsigned index);

public:
  static TermList invertTop(const InversionContext& ctxt);

  static bool canInvertTop(const InversionContext &ctxt);
};

#define __BEGIN__IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Frac)                     \
  template <>                                                                  \
  bool NumberTheoryInverter<Frac##ConstantType>::canInvertTop(                 \
      const InversionContext &ctxt) {                                          \
      CALL("NumberTheoryInverter::canInvertTop") \
    auto &t = ctxt.topTerm();                                         \
    auto index = ctxt.topIdx();                                     \
    auto fun = t.functor();                              \
                                                                               \
    if (theory->isInterpretedFunction(fun)) {                                  \
      auto inter = theory->interpretFunction(fun);                             \
      switch (inter) {

#define __END__IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Frac)                       \
  default:                                                                     \
    DEBUG("WARNING: unknown interpreted function: " << t)                      \
    return false;                                                              \
    }                                                                          \
    }                                                                          \
    else {                                                                     \
      /* cannot invert uninterpreted functions */                              \
      return false;                                                            \
    }                                                                          \
    }

#define IMPL_NUM_THEORY_INVERTER_INVERT(Frac, ...)                             \
  template <>                                                                  \
  TermList NumberTheoryInverter<Frac##ConstantType>::invertTop(                   \
      const InversionContext& ctxt) {                        \
    auto& t = ctxt.topTerm(); \
    auto index = ctxt.topIdx(); \
    auto toWrap = ctxt.toWrap(); \
    auto fun = t.functor();                                                    \
    ASS(theory->isInterpretedFunction(fun))                                    \
    switch (theory->interpretFunction(fun)) {                                  \
      __VA_ARGS__                                                              \
    default:                                                                   \
      ASSERTION_VIOLATION;                                                     \
    }                                                                          \
  };

#define __INVERT_ADD                                                           \
  case number::addI:                                                           \
    return number::add(toWrap, number::minus(t[1 - index]));

#define __INVERT_MUL                                                           \
  case number::mulI:                                                           \
    return number::mul(toWrap, number::div(number::one(), t[1 - index]));

#define __INVERT_MINUS                                                         \
  case number::minusI:                                                         \
    return number::minus(toWrap);

#define __INVERT_MUL_INT \
  case number::mulI: \
{ \
    IntMulInversion inv; \
    ALWAYS(tryInvertMulInt(ctxt, inv)); \
/** (a * t1) = (t2 * b) 
 * ===================== where a * c = b
 *  t1 = (t2 * c)    
 */ \
    ASS(inv.a.divides(inv.b));\
    auto c = theory->representConstant(inv.b / inv.a);\
    return number::mul(inv.t2, TermList(c)); \
}
    


/** (a * t1) = (t2 * b) 
 *  ^^^^^^^^ ctxt.topTerm()
 *       ^^  ctxt.toUnwrap()
 */
struct IntMulInversion {
  IntegerConstantType a;
  TermList t1; 
  IntegerConstantType b; 
  TermList t2;
};

bool tryInvertMulInt(const InversionContext& ctxt, IntMulInversion& inv) {

  using number = num_traits<IntegerConstantType>;

  auto a_ = ctxt.topTerm()[1 - ctxt.topIdx()];
  IntegerConstantType a;
  if (ctxt.toWrap().isTerm() && theory->tryInterpretConstant(a_, a)) {

    auto& wrap = *ctxt.toWrap().term();
    ASS(ctxt.topTerm().arity() == 2)
    /* (a * t1) = f(...) 
     *             ^^^^^^ wrap
     */

    IntegerConstantType b;

    if (wrap.functor() == ctxt.topTerm().functor()) {
        /* (a * t1) = (_ * _) 
         *            ^^^^^^^ wrap
         */
        for (int i = 0; i < 2; i++) {
          if (theory->tryInterpretConstant(wrap[i], b) && a.divides(b)) {
            inv = IntMulInversion {
              .t1 = ctxt.toUnwrap(),
              .t2 = wrap[1-i],
              .b = b,
              .a = a,
            };
            return true;
          }
        }
      } else if(theory->tryInterpretConstant(&wrap, b) && a.divides(b)) {
        /* (a * t1) = b * 1
         *            ^ wrap
         */
        inv = IntMulInversion {
          .t1 = ctxt.toUnwrap(),
          .t2 = number::one(),
          .a = a,
          .b = b,
        };
        return true;
      }
    }
    return false;
}

template <class number> bool nonZero(const TermList &t) {
  typename number::ConstantType c;
  return theory->tryInterpretConstant(t, c) && number::zeroC != c;
}

#define IMPL_NUM_THEORY_INVERTER_FRAC(Frac)                                    \
  IMPL_NUM_THEORY_INVERTER_INVERT(Frac,                                        \
                                  __INVERT_ADD __INVERT_MINUS __INVERT_MUL)    \
  __BEGIN__IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Frac)                           \
  case number::addI:                                                           \
    return true;                                                               \
  case number::minusI:                                                         \
    return true;                                                               \
  case number::mulI:                                                           \
    return nonZero<number>(t[1 - index]);                                      \
  __END__IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Frac)

IMPL_NUM_THEORY_INVERTER_FRAC(Rational)
IMPL_NUM_THEORY_INVERTER_FRAC(Real)

IMPL_NUM_THEORY_INVERTER_INVERT(Integer, __INVERT_ADD __INVERT_MINUS __INVERT_MUL_INT)



__BEGIN__IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Integer)

case number::addI:
  return true;
case number::minusI:
  return true;
case number::mulI:
{
  ASS(t.arity() == 2)
  IntMulInversion _inv;
  return tryInvertMulInt(ctxt, _inv);
}

__END__IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Integer)

} // namespace Inverters
} // namespace Rebalancing
} // namespace Kernel

#endif // __REBALANCING_INVERTERS_H__
