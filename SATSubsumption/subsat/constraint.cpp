/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "./constraint.hpp"

namespace subsat {


std::ostream& operator<<(std::ostream& os, Constraint const& c)
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

std::ostream& operator<<(std::ostream& os, ConstraintRef cr)
{
  os << "ConstraintRef{";
  if (cr.is_valid()) {
    os << cr.index();
  } else {
    os << "-";
  }
  os << "}";
  return os;
}


} // namespace subsat
