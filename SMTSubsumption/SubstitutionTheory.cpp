/*
 * SubstitutionTheory.cpp
 * Copyright (C) 2020 Jakob Rath <git@jakobrath.eu>
 *
 * Distributed under terms of the MIT license.
 */

#include "SubstitutionTheory.hpp"

namespace SMTSubsumption {


std::ostream& operator<<(std::ostream& o, SubstitutionAtom const& atom)
{
  o << "SubstitutionAtom { ";
  bool first = true;
  for (auto mapping : atom.subst) {
    if (!first) {
      o << ", ";
    } else {
      first = false;
    }
    o << TermList(mapping.first, false).toString() << " -> " << mapping.second.toString();
  }
  o << " }";
  return o;
}


}
