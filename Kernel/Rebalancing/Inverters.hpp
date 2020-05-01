#ifndef __REBALANCING_INVERTERS_H__
#define __REBALANCING_INVERTERS_H__

#include <iostream>
#include "Lib/Environment.hpp"
#include "Forwards.hpp"

#include "Kernel/num_traits.hpp"

namespace Kernel {
  namespace Rebalancing {
    namespace Inverters {

      template<class C>
      class NumberTheoryInverter {
        using number = num_traits<C>;

        static bool canInvert(Interpretation i, const Term& t, unsigned index);
      public:

        static TermList invert(const Term& t, unsigned index, TermList toWrap);
        // {
        //   auto fun = t.functor();
        //   ASS(theory->isInterpretedFunction(fun))
        //
        // }

        static bool canInvert(const Term& t, unsigned index) {
          auto fun = t.functor();

          if (theory->isInterpretedFunction(fun)) {
            auto i = theory->interpretFunction(fun);
            auto out = canInvert(i,t,index);
            DEBUG("########### canInvert(" << t << "@" << index << ") -> " << out)
            return out;
            
          } else {
            /* cannot invert uninterpreted functions */
            return false;
          }
        }
      };

#define IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Frac, ...) \
      template<> bool NumberTheoryInverter<Frac ## ConstantType>::canInvert( \
          Interpretation inter,  \
          const Term& t,  \
          unsigned index)  \
      { \
        switch (inter) { \
            __VA_ARGS__ \
          default: \
            DEBUG("WARNING: unknown interpreted function: " << t) \
            return false; \
        } \
      }; \

#define IMPL_NUM_THEORY_INVERTER_INVERT(Frac, ...) \
      template<> TermList NumberTheoryInverter<Frac ## ConstantType>::invert( \
          const Term& t,  \
          unsigned index, \
          TermList toWrap )  \
      { \
        auto fun = t.functor(); \
        ASS(theory->isInterpretedFunction(fun)) \
        switch (theory->interpretFunction(fun)) { \
            __VA_ARGS__ \
          default: \
            ASSERTION_VIOLATION; \
        } \
      }; \

#define __INVERT_ADD \
    case number::addI:  \
      return number::add(toWrap, number::minus(t[1 - index])); \

#define __INVERT_MUL \
    case number::mulI:  \
      return number::mul(toWrap, number::div(number::one(), t[1 - index]));

#define __INVERT_MINUS \
    case number::minusI:  \
      return number::minus(toWrap); \


      template<class number>
      bool nonZero(const TermList& t) {
        typename number::ConstantType c;
        return theory->tryInterpretConstant(t,c) && number::zeroC != c;
      }

#define IMPL_NUM_THEORY_INVERTER_FRAC(Frac) \
      IMPL_NUM_THEORY_INVERTER_INVERT(Frac,  \
          __INVERT_ADD \
          __INVERT_MINUS \
          __INVERT_MUL \
          ) \
      IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Frac, \
          case number::addI: \
          case number::minusI: \
            return true; \
          case number::mulI: \
            return nonZero<number>(t[1 - index]);\
        )\

      IMPL_NUM_THEORY_INVERTER_FRAC(Rational)
      IMPL_NUM_THEORY_INVERTER_FRAC(Real)


      IMPL_NUM_THEORY_INVERTER_INVERT(Integer, 
          __INVERT_ADD
          __INVERT_MINUS
          )

      IMPL_NUM_THEORY_INVERTER_CAN_INVERT(Integer, 
          case number::addI: 
          case number::minusI: 
            return true; 
          case number::mulI: 
            ASS(t.arity() == 2)
            /* (a * b) = ( c * d ) */
            // number::ConstantType b;
            // if (theory->tryInterpretConstant(other, t[1 - index])) {
            //   return false;
            // } else {
            //   return false;
            // }
            return false; //TODO
        )


    }
  }
}

#endif // __REBALANCING_INVERTERS_H__
