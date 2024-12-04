/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file TermPartialOrdering.hpp
 * Defines class TermPartialOrdering.
 */

#ifndef __TermPartialOrdering__
#define __TermPartialOrdering__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"

#include "Ordering.hpp"
#include "PartialOrdering.hpp"

namespace Kernel {

using namespace Lib;
using Result = Ordering::Result;

class TermPartialOrdering
{
public:
  TermPartialOrdering(const Ordering& ord) : _ord(ord), _po(PartialOrdering::getEmpty()) {}
  ~TermPartialOrdering() = default;

  bool get(TermList lhs, TermList rhs, Result& res) const;
  bool set(Ordering::Constraint con);

  static const TermPartialOrdering* getEmpty(const Ordering& ord);
  static const TermPartialOrdering* set(const TermPartialOrdering* tpo, Ordering::Constraint con);

  // Returns if PO contains full incomparability yet.
  // Useful to discard branches when reasoning over ground terms.
  bool hasIncomp() const;

  std::string to_string() const;
  std::string to_nice_string() const;

private:
  PoComp get_one_external(TermList t, size_t idx) const;
  PoComp get_two_external(TermList t1, TermList t2) const;

  size_t idx_of_elem(TermList t) const;
  size_t idx_of_elem_ext(TermList t);

#if DEBUG_ORDERING
  void debug_check() const;
#endif

  const Ordering& _ord;
  Map<TermList,size_t> _nodes;
  const PartialOrdering* _po;
};

};

#endif /* __PartialOrdering__ */