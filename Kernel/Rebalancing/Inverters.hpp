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

#define IMPL_NUM_THEORY_INVERTER(Frac, ...) \
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

      IMPL_NUM_THEORY_INVERTER(Rational, 
          case number::addI: 
          case number::minusI: 
          case number::mulI: 
            return true; 
        )

      IMPL_NUM_THEORY_INVERTER(Real, 
          case number::addI: 
          case number::minusI: 
          case number::mulI: 
            return true; 
        )

      IMPL_NUM_THEORY_INVERTER(Integer, 
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
