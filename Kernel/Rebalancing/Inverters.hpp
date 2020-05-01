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
      class NumberInverter {
        using number = num_traits<C>;
      public:
        static bool canInvert(const Term& t, unsigned index) {
          return true;
        }
      };

    }
  }
}

#endif // __REBALANCING_INVERTERS_H__
