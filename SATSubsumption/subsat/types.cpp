/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "./types.hpp"

namespace subsat {


std::ostream& operator<<(std::ostream& os, Value v)
{
  switch (v) {
    case Value::False:
      os << "false";
      break;
    case Value::Unassigned:
      os << "unassigned";
      break;
    case Value::True:
      os << "true";
      break;
#if NDEBUG
    default:
      os << "illegal(" << static_cast<std::underlying_type<Result>::type>(v) << ")";
      break;
#endif
  }
  return os;
}

std::ostream& operator<<(std::ostream& os, Result r)
{
  switch (r) {
    case Result::Sat:
      os << "sat";
      break;
    case Result::Unsat:
      os << "unsat";
      break;
    case Result::Unknown:
      os << "unknown";
      break;
#if NDEBUG
    default:
      os << "illegal(" << static_cast<std::underlying_type<Result>::type>(r) << ")";
      break;
#endif
  }
  return os;
}

std::ostream& operator<<(std::ostream& os, Var var)
{
  if (var.is_valid()) {
    os << var.index();
  } else {
    os << "-";
  }
  return os;
}

std::ostream& operator<<(std::ostream& os, Lit lit)
{
  if (lit.is_valid()) {
    if (lit.is_negative()) {
      os << '~';
    }
    os << lit.var();
  } else {
    os << "-";
  }
  return os;
}


}  // namespace subsat
