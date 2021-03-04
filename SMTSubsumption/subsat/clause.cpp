#include "./clause.hpp"

namespace subsat {


std::ostream& operator<<(std::ostream& os, Clause const& c)
{
  os << "{ ";
  bool first = true;
  for (Lit lit : c) {
    if (first) {
      first = false;
    } else {
      os << ", ";
    }
    os << lit;
  }
  os << " }";
  return os;
}

std::ostream& operator<<(std::ostream& os, ClauseRef cr)
{
  os << "ClauseRef{";
  if (cr.is_valid()) {
    os << cr.index();
  } else {
    os << "-";
  }
  os << "}";
  return os;
}


} // namespace subsat
