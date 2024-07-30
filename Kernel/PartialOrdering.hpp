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

using PoComp = Ordering::Result;

// enum class PoComp {
//   INC=0,
//   EQ=1,
//   GT=2,
//   LT=3,
// };

// PoComp reverse(PoComp comp);
// std::string toString(PoComp comp);

struct Edge {
  unsigned x;
  unsigned y;
  PoComp c;

  std::tuple<unsigned,unsigned,PoComp> asTuple() const
  { return std::make_tuple(x, y, c); }

  IMPL_COMPARISONS_FROM_TUPLE(Edge);
  IMPL_HASH_FROM_TUPLE(Edge);
};

template<typename T> 
class PartialOrdering
{
public:
  PartialOrdering();
  PartialOrdering(const PartialOrdering& other);
  ~PartialOrdering();

  PartialOrdering& operator=(const PartialOrdering& other);

  bool is_total() const;
  size_t size() const { return _size; }
  const List<Edge>* transitive_reduction() const { return _tr; }
  PoComp get(const T& x, const T& y) const;
  bool set(const T& x, const T& y, PoComp v);
  const T& get_rep(const T& e) const;

  std::string to_string() const;
  std::string to_string_raw() const;

  VirtualIterator<std::tuple<T,T,PoComp>> iter_relations() const;
  bool subseteq(const PartialOrdering& other) const;

private:
  size_t idx_of_elem(const T& e) const;
  size_t idx_of_elem_ext(const T& e);
  PoComp idx_of(size_t idx_x, size_t idx_y) const;
  void set_idx_of(size_t idx_x, size_t idx_y, PoComp v);
  void set_idx_of_safe(size_t idx_x, size_t idx_y, PoComp v);

  void set_inferred(size_t idx_x, size_t idx_y, PoComp result);
  void set_inferred_loop(size_t idx_x, size_t idx_y, PoComp gt, PoComp lt);
  void set_inferred_loop_eq(size_t idx_x, size_t idx_y);

  DHMap<T,size_t> _nodes;
  DHMap<size_t,T> _inverse;
  size_t _size;
  PoComp* _array;
  List<Edge>* _tr; // transitive reduction
};

};

#endif /* __PartialOrdering__ */