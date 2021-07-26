/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "Rebalancing.hpp"

namespace Kernel {
namespace Rebalancing {

std::ostream& operator<<(std::ostream& out, const Node& n) {
  out << n.term() << "@" << n.index();
  return out;
}

std::ostream& operator<<(std::ostream& out, const InversionContext& n) {
  out << n._toInvert << "@" << n._unwrapIdx << " = " << n._toWrap;
  return out;
}

} //namespace Kernel 
} // namespace Rebalancing 
