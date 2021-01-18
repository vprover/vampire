
  /*
   * File Inverters.hpp.
   *
   * This file is part of the source code of the software program
   * Vampire. It is protected by applicable
   * copyright laws.
   *
   * This source code is distributed under the licence found here
   * https://vprover.github.io/license.html
   * and in the source directory
   */

#ifndef __REBALANCING_INVERTERS_H__
#define __REBALANCING_INVERTERS_H__

#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Option.hpp"
#include "Kernel/Rebalancing.hpp"
#include <iostream>

#include "Kernel/NumTraits.hpp"

namespace Kernel {
namespace Rebalancing {
namespace Inverters {

class NumberTheoryInverter {
  const bool _generateGuards;

public:

  NumberTheoryInverter(bool generateGuards) : _generateGuards(generateGuards) {}
  InversionResult invertTop(const InversionContext &ctxt) const;
  bool canInvertTop(const InversionContext &ctxt) const;
private: 

  bool tryInvertTop(const InversionContext &ctxt, InversionResult *out) const;
  void addGuard(Literal* lit);

  template<class NumTraits> InversionResult doInvertDiv(const InversionContext &ctxt) const;
  template<class NumTraits> bool canInvertDiv(const InversionContext &ctxt) const;
  template<class NumTraits> bool tryInvertDiv(const InversionContext &ctxt, InversionResult *out) const;
};

} // namespace Inverters
} // namespace Rebalancing
} // namespace Kernel

#endif // __REBALANCING_INVERTERS_H__
