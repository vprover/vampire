#ifndef __REBALANCING_INVERTERS_H__
#define __REBALANCING_INVERTERS_H__

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Kernel/Rebalancing.hpp"
#include <iostream>

#include "Kernel/NumTraits.hpp"

namespace Kernel {
namespace Rebalancing {
namespace Inverters {

class NumberTheoryInverter {
  static bool canInvertTop(Interpretation i, const Term &t, unsigned index);

public:
  static TermList invertTop(const InversionContext &ctxt);
  static bool canInvertTop(const InversionContext &ctxt);
};

} // namespace Inverters
} // namespace Rebalancing
} // namespace Kernel

#endif // __REBALANCING_INVERTERS_H__
