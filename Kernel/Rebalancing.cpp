
#include "Rebalancing.hpp"

namespace Kernel {
namespace Rebalancing {

std::ostream& operator<<(std::ostream& out, const Node& n) {
  out << n.term() << "@" << n.index();
  return out;
}

} //namespace Kernel 
} // namespace Rebalancing 
