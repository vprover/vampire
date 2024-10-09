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
 * @file PartialOrdering.hpp
 * Defines class PartialOrdering.
 */

#ifndef __PartialOrdering__
#define __PartialOrdering__

#include "Forwards.hpp"

#include "Lib/DHMap.hpp"
#include "Lib/VirtualIterator.hpp"

#include "Ordering.hpp"

namespace Kernel {

using namespace Lib;

using Result = Ordering::Result;

enum class PoComp : uint8_t {
  UNKNOWN,
  GREATER,
  EQUAL,
  LESS,
  LTR_INCOMPARABLE,
  RTL_INCOMPARABLE,
  INCOMPARABLE,
};

class PartialOrdering
{
public:
  PartialOrdering();
  PartialOrdering(const PartialOrdering& other);
  ~PartialOrdering();

  void reset();

  bool get(TermList lhs, TermList rhs, Ordering::Result& res) const;
  bool set(Ordering::Constraint con);

  std::string to_string() const;
  std::string to_string_raw() const;

private:
  size_t idx_of_elem(TermList t) const;
  size_t idx_of_elem_ext(TermList t);
  PoComp idx_of(size_t x, size_t y) const;
  void set_idx_of(size_t x, size_t y, PoComp v);
  void set_idx_of_safe(size_t x, size_t y, PoComp v);

  void set_inferred(size_t x, size_t y, PoComp result);
  void set_inferred_loop(size_t x, size_t y, PoComp rel);
  void set_inferred_loop_eq(size_t x, size_t y);

  DHMap<TermList,size_t> _nodes;
  DHMap<size_t,TermList> _inverse;
  size_t _size;
  PoComp* _array;
};

};

#endif /* __PartialOrdering__ */