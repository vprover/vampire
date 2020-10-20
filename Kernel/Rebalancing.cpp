
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
