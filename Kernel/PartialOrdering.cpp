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
 * @file PartialOrdering.cpp
 * Implements class PartialOrdering.
 */

#include <cstring>
#include <iomanip>

#include "PartialOrdering.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Metaiterators.hpp"

#define RETURN_IF_FAIL(Cond) \
  {                          \
    if (!(Cond)) {           \
      return false;          \
    }                        \
  }

namespace Kernel {

using namespace std;

constexpr PoComp reverse(PoComp v) {
  switch (v) {
    case PoComp::UNKNOWN:
      return PoComp::UNKNOWN;
    case PoComp::GREATER:
      return PoComp::LESS;
    case PoComp::EQUAL:
      return PoComp::EQUAL;
    case PoComp::LESS:
      return PoComp::GREATER;
    case PoComp::NGEQ:
      return PoComp::NLEQ;
    case PoComp::NLEQ:
      return PoComp::NGEQ;
    case PoComp::INCOMPARABLE:
      return PoComp::INCOMPARABLE;
  }
}

constexpr PoComp weaken(PoComp v) {
  switch (v) {
    case PoComp::GREATER:
      return PoComp::NLEQ;
    case PoComp::LESS:
      return PoComp::NGEQ;
    default:
      ASSERTION_VIOLATION;
  }
}

constexpr PoComp strengthen(PoComp v) {
  switch (v) {
    case PoComp::NLEQ:
      return PoComp::GREATER;
    case PoComp::NGEQ:
      return PoComp::LESS;
    default:
      ASSERTION_VIOLATION;
  }
}

Result poCompToResult(PoComp c) {
  switch (c) {
    case PoComp::GREATER:
      return Result::GREATER;
    case PoComp::EQUAL:
      return Result::EQUAL;
    case PoComp::LESS:
      return Result::LESS;
    case PoComp::NGEQ:
    case PoComp::NLEQ:
    case PoComp::INCOMPARABLE:
      return Result::INCOMPARABLE;
    default:
      break;
  }
  ASSERTION_VIOLATION;
}

PoComp resultToPoComp(Result r, bool reversed) {
  switch (r) {
    case Result::GREATER:
      return reversed ? PoComp::LESS : PoComp::GREATER;
    case Result::EQUAL:
      return PoComp::EQUAL;
    case Result::LESS:
      return reversed ? PoComp::GREATER : PoComp::LESS;
    case Result::INCOMPARABLE:
      return reversed ? PoComp::NLEQ : PoComp::NGEQ;
  }
}

PartialOrdering::PartialOrdering(const Ordering& ord)
  : _ord(ord), _nodes(), _size(0), _array(nullptr), _hasIncomp(false), _prev(nullptr) {}

PartialOrdering::PartialOrdering(const PartialOrdering& other)
  : _ord(other._ord), _nodes(other._nodes), _size(_nodes.size()), _array(nullptr), _hasIncomp(other._hasIncomp), _prev(&other)
{
  size_t arrSize = ((_size - 1) * _size / 2);
  if (arrSize) {
    void* mem = ALLOC_KNOWN(arrSize*sizeof(PoComp), "Kernel::PartialOrdering");
    _array = array_new<PoComp>(mem, arrSize);
    memcpy(_array,other._array,arrSize*sizeof(PoComp));
  }
}

PartialOrdering::~PartialOrdering()
{
  size_t arrSize = ((_size - 1) * _size / 2);
  if (arrSize) {
    array_delete(_array, arrSize);
    DEALLOC_KNOWN(_array, arrSize*sizeof(PoComp), "Kernel::PartialOrdering");
  }
}

PoComp PartialOrdering::get_one_external(TermList t, size_t idx) const
{
  PoComp res = PoComp::UNKNOWN;
  decltype(_nodes)::Iterator it(_nodes);
  while (it.hasNext()) {
    auto& e = it.next();
    if (e.value()==idx) {
      continue;
    }
    auto val = idx_of_safe(e.value(),idx);
    if (val == PoComp::UNKNOWN) {
      continue;
    }
    auto comp = _ord.compare(t,e.key());
    switch (comp) {
      case Ordering::GREATER: {
        switch (val) {
          case PoComp::EQUAL:
          case PoComp::GREATER:
            // t > e ≥ x -> t > x
            ALWAYS(checkCompatibility(res, PoComp::GREATER, res));
          case PoComp::NLEQ:
          case PoComp::INCOMPARABLE:
            // t > e ≰ x -> t ≰ x
            ALWAYS(checkCompatibility(res, PoComp::NLEQ, res));
          default:
            break;
        }
        break;
      }
      case Ordering::EQUAL: {
        return val;
      }
      case Ordering::LESS: {
        switch (val) {
          case PoComp::EQUAL:
          case PoComp::LESS:
            // t < e ≤ x -> t < x
            ALWAYS(checkCompatibility(res, PoComp::LESS, res));
          case PoComp::NGEQ:
          case PoComp::INCOMPARABLE:
            // t < e ≱ x -> t ≱ x
            ALWAYS(checkCompatibility(res, PoComp::NGEQ, res));
          default:
            break;
        }
        break;
      }
      case Ordering::INCOMPARABLE: {
        break;
      }
    }
  }
  return res;
}

PoComp PartialOrdering::get_two_external(TermList t1, TermList t2) const
{
  PoComp res = PoComp::UNKNOWN;
  Stack<pair<size_t,Ordering::Result>> t1_rel; // ∃x. t1 rel x
  Stack<pair<size_t,Ordering::Result>> t2_rel; // ∃x. x rel t2

  decltype(_nodes)::Iterator it(_nodes);
  while (it.hasNext()) {
    auto& e = it.next();
    auto comp1 = _ord.compare(t1,e.key());
    if (comp1 != Ordering::INCOMPARABLE) {
      t1_rel.push({ e.value(), comp1 });
    }
    auto comp2 = _ord.compare(e.key(),t2);
    if (comp2 != Ordering::INCOMPARABLE) {
      t2_rel.push({ e.value(), comp2 });
    }
  }
  for (const auto& [e1,r1] : t1_rel) {
    for (const auto& [e2,r2] : t2_rel) {
      auto r = e1 == e2 ? PoComp::EQUAL : idx_of_safe(e1,e2);
      switch (r) {
        case PoComp::UNKNOWN:
          break;
        case PoComp::EQUAL: {
          switch (r1) {
            case Ordering::GREATER: {
              if (r2 != Ordering::LESS) {
                // t1 > e1 = e2 ≥ t2 -> t1 > t2
                ALWAYS(checkCompatibility(res, PoComp::GREATER, res));
              }
              break;
            }
            case Ordering::EQUAL: {
              // t1 = e1 = e2 r2 t2 -> t1 r2 t2
              ALWAYS(checkCompatibility(res, resultToPoComp(r2, false), res));
              break;
            }
            case Ordering::LESS: {
              if (r2 != Ordering::GREATER) {
                // t1 < e1 = e2 ≤ t2 -> t1 < t2
                ALWAYS(checkCompatibility(res, PoComp::LESS, res));
              }
              break;
            }
            case Ordering::INCOMPARABLE:
              ASSERTION_VIOLATION;
          }
          break;
        }
        case PoComp::GREATER:
        case PoComp::NLEQ: {
          if (r1 != Ordering::LESS && r2 != Ordering::LESS) {
            // t1 ≥ e1 > e2 ≥ t2 -> t1 > t2
            // t1 ≥ e1 ≰ e2 ≥ t2 -> t1 ≰ t2
            ALWAYS(checkCompatibility(res, r, res));
          }
          break;
        }
        case PoComp::LESS:
        case PoComp::NGEQ: {
          if (r1 != Ordering::GREATER && r2 != Ordering::GREATER) {
            // t1 ≤ e1 < e2 ≤ t2 -> t1 < t2
            // t1 ≤ e1 ≱ e2 ≤ t2 -> t1 ≱ t2
            ALWAYS(checkCompatibility(res, r, res));
          }
          break;
        }
        case PoComp::INCOMPARABLE: {
          if (r1 != Ordering::GREATER && r2 != Ordering::GREATER) {
            // t1 ≤ e1 ≱ e2 ≤ t2 -> t1 ≱ t2
            ALWAYS(checkCompatibility(res, PoComp::NGEQ, res));
          }
          if (r1 != Ordering::LESS && r2 != Ordering::LESS) {
            // t1 ≥ e1 ≰ e2 ≥ t2 -> t1 ≰ t2
            ALWAYS(checkCompatibility(res, PoComp::NLEQ, res));
          }
          break;
        }
      }
    }
  }
  return res;
}

bool PartialOrdering::get(TermList lhs, TermList rhs, Result& res) const
{
  // comparable terms should be handled by caller
  ASS_EQ(_ord.compare(lhs,rhs),Ordering::INCOMPARABLE);
  // proper term pairs should be handled by caller 
  ASS(lhs.isVar() || rhs.isVar());

  if (lhs == rhs) {
    res = Result::EQUAL;
    return true;
  }
  PoComp val;
  bool reversed = false;
  if (!_nodes.find(lhs) && !_nodes.find(rhs))
  {
    val = get_two_external(lhs, rhs);
  }
  else if (!_nodes.find(lhs))
  {
    ASS(_nodes.find(rhs));
    size_t y = idx_of_elem(rhs);
    val = get_one_external(lhs, y);
  }
  else if (!_nodes.find(rhs))
  {
    ASS(_nodes.find(lhs));
    size_t x = idx_of_elem(lhs);
    val = get_one_external(rhs, x);
    reversed = true;
  }
  else
  {
    size_t x = idx_of_elem(lhs);
    size_t y = idx_of_elem(rhs);
    reversed = x > y;
    if (reversed) {
      swap(x,y);
    }
    val = idx_of(x,y);
  }
  if (val == PoComp::UNKNOWN) {
    return false;
  }
  // if we only have INCOMPARABLE in the "other direction"
  // as we use isGreater which never gives LESS, we cannot
  // distinguish between the two LESS and INCOMPARABLE
  if (reversed) {
    if (val == PoComp::NGEQ) {
      return false;
    }
    res = Ordering::reverse(poCompToResult(val));
    return true;
  } else {
    if (val == PoComp::NLEQ) {
      return false;
    }
    res = poCompToResult(val);
    return true;
  }
}

bool checkCompatibility(PoComp old, PoComp curr, PoComp& res)
{
  if (old == PoComp::UNKNOWN) {
    res = curr;
    return true;
  }
  switch (curr) {
    case PoComp::GREATER:
      res = PoComp::GREATER;
      return old == PoComp::GREATER || old == PoComp::NLEQ;
    case PoComp::EQUAL:
      res = PoComp::EQUAL;
      return old == PoComp::EQUAL;
    case PoComp::LESS:
      res = PoComp::LESS;
      return old == PoComp::LESS || old == PoComp::NGEQ;
    case PoComp::INCOMPARABLE:
      res = PoComp::INCOMPARABLE;
      return old == PoComp::INCOMPARABLE || old == PoComp::NGEQ || old == PoComp::NLEQ;
    case PoComp::NGEQ:
      switch (old) {
        case PoComp::LESS:
        case PoComp::INCOMPARABLE:
        case PoComp::NGEQ:
          res = old;
          return true;
        case PoComp::NLEQ:
          res = PoComp::INCOMPARABLE;
          return true;
        default:
          return false;
      }
      break;
    case PoComp::NLEQ:
      switch (old) {
        case PoComp::GREATER:
        case PoComp::INCOMPARABLE:
        case PoComp::NLEQ:
          res = old;
          return true;
        case PoComp::NGEQ:
          res = PoComp::INCOMPARABLE;
          return true;
        default:
          return false;
      }
      break;
    default:
      ASSERTION_VIOLATION;
  }
  ASSERTION_VIOLATION;
}

bool PartialOrdering::set(Ordering::Constraint con)
{
  ASS_EQ(_size,_nodes.size());
  if (con.lhs == con.rhs) {
    return true; // TODO should we check anything here?
  }
  size_t x = idx_of_elem_ext(con.lhs);
  size_t y = idx_of_elem_ext(con.rhs);

  bool reversed = x > y;
  if (reversed) {
    swap(x,y);
  }
  PoComp new_val = resultToPoComp(con.rel, reversed);

  bool changed;
  RETURN_IF_FAIL(set_idx_of(x, y, new_val, changed));

  // if something's changed, we calculate the transitive closure
  if (changed) {
    RETURN_IF_FAIL(set_inferred(x, y, new_val));
  }
#if DEBUG_ORDERING
  // debug_check();
#endif
  return true;
}

size_t PartialOrdering::idx_of_elem(TermList t) const
{
  ASS(_nodes.find(t));
  return _nodes.get(t);
}

size_t PartialOrdering::idx_of_elem_ext(TermList t)
{
  size_t *ptr;
  if (_nodes.getValuePtr(t, ptr, _size)) {
    // extend array
    size_t prevSize = ((_size - 1) * _size / 2);
    auto prevArray = _array;
    _size++;
    if (_size>1) {
      size_t newSize = prevSize + _size;
      void* mem = ALLOC_KNOWN(newSize*sizeof(PoComp), "Kernel::PartialOrdering");
      _array = array_new<PoComp>(mem, newSize);
      std::memset(_array, 0, newSize*sizeof(PoComp));
      if (prevArray) {
        memcpy(_array,prevArray,prevSize*sizeof(PoComp));
      }
    }
    // remove previous array
    if (prevSize) {
      array_delete(prevArray, prevSize);
      DEALLOC_KNOWN(prevArray, prevSize*sizeof(PoComp), "Kernel::PartialOrdering");
    }

    // fill out new row with known values
    size_t idx = _size-1;
    decltype(_nodes)::Iterator it(_nodes);
    while (it.hasNext()) {
      auto& e = it.next();
      if (e.value()==idx) {
        continue;
      }
      auto comp = _ord.compare(e.key(),t);
      if (comp == Ordering::INCOMPARABLE) {
        continue;
      }
      auto val = resultToPoComp(comp, false);
      bool unused;
      ALWAYS(set_idx_of(e.value(), idx, val, unused));
      ALWAYS(set_inferred(e.value(), idx, val));
    }
  }
  return *ptr;
}

bool PartialOrdering::set_idx_of(size_t x, size_t y, PoComp v, bool& changed)
{
  size_t idx = y*(y-1)/2 + x;
  ASS_L(idx,((_size - 1) * _size / 2));
  PoComp new_v;
  if (!checkCompatibility(_array[idx], v, new_v)) {
    changed = false;
    return false;
  }
  changed = (_array[idx] != new_v);
  _array[idx] = new_v;
  if (new_v == PoComp::INCOMPARABLE) {
    _hasIncomp = true;
  }
  return true;
}

bool PartialOrdering::set_idx_of_safe(size_t x, size_t y, PoComp v, bool& changed)
{
  if (x < y) {
    return set_idx_of(x,y,v,changed);
  } else {
    return set_idx_of(y,x,reverse(v),changed);
  }
}

PoComp PartialOrdering::idx_of(size_t x, size_t y) const
{
  size_t idx = y*(y-1)/2 + x;
  ASS_L(idx,((_size - 1) * _size / 2));
  return _array[idx];
}

PoComp PartialOrdering::idx_of_safe(size_t x, size_t y) const
{
  if (x < y) {
    return idx_of(x,y);
  } else {
    return reverse(idx_of(y,x));
  }
}

bool PartialOrdering::set_inferred_loop(size_t x, size_t y, PoComp rel)
{
  ASS_NEQ(x,y);

  Stack<size_t> above;
  Stack<size_t> above_w;
  Stack<size_t> below;
  Stack<size_t> below_w;
  auto wkn = weaken(rel); // weakened variant of rel
  bool changed;

  for (size_t z = 0; z < _size; z++) {
    if (z == x || z == y) {
      continue;
    }
    auto r = idx_of_safe(z, x);
    // if rel = ≤: z ≤ x  ∧  x ≤ y  →  z ≤ y
    // if rel = ≥: z ≥ x  ∧  x ≥ y  →  z ≥ y
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(set_idx_of_safe(z, y, rel, changed));
      if (changed) {
        above.push(z);
        // TODO find out why we should continue here
        // continue;
      }
    }
    // if rel = ≤: z ≱ x  ∧  x ≤ y  →  z ≱ y
    // if rel = ≥: z ≰ x  ∧  x ≥ y  →  z ≰ y
    else if (r == wkn || r == PoComp::INCOMPARABLE) {
      RETURN_IF_FAIL(set_idx_of_safe(z, y, wkn, changed));
      if (changed) {
        above_w.push(z);
        // TODO find out why we should continue here
        // continue;
      }
    }

    r = idx_of_safe(y, z);
    // x rel y  ∧  y rel z  →  x rel z
    // x rel y  ∧  y  =  z  →  x rel z
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(set_idx_of_safe(x, z, rel, changed));
      if (changed) {
        below.push(z);
      }
    }
    // x rel y  ∧  y wkn z  →  x wkn z
    // x rel y  ∧  y inc z  →  x wkn z
    else if (r == wkn || r == PoComp::INCOMPARABLE) {
      RETURN_IF_FAIL(set_idx_of_safe(x, z, wkn, changed));
      if (changed) {
        below_w.push(z);
      }
    }
  }

  // connect all pairs that have been derived
  for (const auto& z : above) {
    for (const auto& u : below) {
      RETURN_IF_FAIL(set_idx_of_safe(z,u,rel,changed));
    }
    for (const auto& u : below_w) {
      RETURN_IF_FAIL(set_idx_of_safe(z,u,wkn,changed));
    }
  }
  for (const auto& z : above_w) {
    for (const auto& u : below) {
      RETURN_IF_FAIL(set_idx_of_safe(z,u,wkn,changed));
    }
  }
  return true;
}

bool PartialOrdering::set_inferred_loop_inc(size_t x, size_t y, PoComp wkn)
{
  ASS_NEQ(x,y);

  Stack<size_t> above;
  Stack<size_t> below;
  auto rel = strengthen(wkn); // stronger variant of wkn
  bool changed;

  for (size_t z = 0; z < _size; z++) {
    if (z == x || z == y) {
      continue;
    }
    auto r = idx_of_safe(z, x);
    // z ≤ x  ∧  x ≱ y  →  z ≱ y
    // z ≥ x  ∧  x ≰ y  →  z ≰ y
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(set_idx_of_safe(z, y, wkn, changed));
      if (changed) {
        above.push(z);
        // TODO find out why we should continue here
        // continue;
      }
    }
    r = idx_of_safe(y, z);
    // x ≱ y  ∧  y ≤ z  →  x ≱ z
    // x ≰ y  ∧  y ≥ z  →  x ≰ z
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(set_idx_of_safe(x, z, wkn, changed));
      if (changed) {
        below.push(z);
      }
    }
  }

  // connect all pairs that have been derived
  for (const auto& z : above) {
    for (const auto& u : below) {
      RETURN_IF_FAIL(set_idx_of_safe(z,u,wkn,changed));
    }
  }
  return true;
}

bool PartialOrdering::set_inferred_loop_eq(size_t x, size_t y)
{
  ASS_NEQ(x,y);

  // pairs (z, rel) s.t. z rel x
  Stack<pair<size_t,PoComp>> x_rel;
  // pairs (z, rel) s.t. y rel z
  Stack<pair<size_t,PoComp>> y_rel;
  bool changed;

  for (size_t z = 0; z < _size; z++) {
    if (z == x || z == y) {
      continue;
    }
    auto r = idx_of_safe(z, x);
    if (r != PoComp::UNKNOWN) {
      RETURN_IF_FAIL(set_idx_of_safe(z, y, r, changed));
      if (changed) {
        x_rel.push({ z, r });
        // TODO find out why we should continue here
        // continue;
      }
    }
    r = idx_of_safe(y, z);
    if (r != PoComp::UNKNOWN) {
      RETURN_IF_FAIL(set_idx_of_safe(x, z, r, changed));
      if (changed) {
        y_rel.push({ z, r });
      }
    }
  }

  if (y_rel.isEmpty()) {
    return true;
  }

  // we assume x = y
  for (const auto& [z,rz] : x_rel) {
    switch (rz) {
      case PoComp::EQUAL: {
        for (const auto& [u,ru] : y_rel) {
          // z = x  ∧  x ru u  →  z ru u
          RETURN_IF_FAIL(set_idx_of_safe(z, u, ru, changed));
        }
        break;
      }
      case PoComp::GREATER: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z > x  ∧  x ≥ u  →  z > u
            case PoComp::EQUAL:
            case PoComp::GREATER:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::GREATER, changed));
              break;
            // z > x  ∧  x ≰ u  →  z ≰ u
            case PoComp::NLEQ:
            case PoComp::INCOMPARABLE:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::NLEQ, changed));
              break;
            // z > x  ∧  x < u implies nothing
            case PoComp::LESS:
            // z > x  ∧  x ≱ u implies nothing
            case PoComp::NGEQ:
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }
        break;
      }
      case PoComp::LESS: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z < x  ∧  x ≤ u  →  z < u
            case PoComp::EQUAL:
            case PoComp::LESS:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::LESS, changed));
              break;
            // z < x  ∧  x ≱ u  →  z ≱ u
            case PoComp::NGEQ:
            case PoComp::INCOMPARABLE:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::NGEQ, changed));
              break;
            // z < x  ∧  x > u implies nothing
            case PoComp::GREATER:
            // z < x  ∧  x ≰ u implies nothing
            case PoComp::NLEQ:
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }
        break;
      }
      case PoComp::INCOMPARABLE: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z ≰ x  ∧  x > u  →  z ≰ u
            case PoComp::GREATER:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::NLEQ, changed));
              break;
            // z ⋈ x  ∧  x = u  →  z ⋈ u
            case PoComp::EQUAL:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::INCOMPARABLE, changed));
              break;
            // z ≱ x  ∧  x < u  →  z ≱ u
            case PoComp::LESS:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::NGEQ, changed));
              break;
            // z ⋈ x  ∧  x ≱ u implies nothing
            case PoComp::NGEQ:
            // z ⋈ x  ∧  x ≰ u implies nothing
            case PoComp::NLEQ:
            // z ⋈ x  ∧  x ⋈ u implies nothing
            case PoComp::INCOMPARABLE:
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }
        break;
      }
      case PoComp::NGEQ: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z ≱ x  ∧  x ≤ u  →  z ≱ u
            case PoComp::EQUAL:
            case PoComp::LESS:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::NGEQ, changed));
              break;
            // z ≱ x  ∧  x > u implies nothing
            case PoComp::GREATER:
            // z ≱ x  ∧  x ≱ u implies nothing
            case PoComp::NGEQ:
            // z ≱ x  ∧  x ≰ u implies nothing
            case PoComp::NLEQ:
            // z ≱ x  ∧  x ⋈ u implies nothing
            case PoComp::INCOMPARABLE:
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }
        break;
      }
      case PoComp::NLEQ: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z ≰ x  ∧  x ≥ u  →  z ≰ u
            case PoComp::GREATER:
            case PoComp::EQUAL:
              RETURN_IF_FAIL(set_idx_of_safe(z, u, PoComp::NLEQ, changed));
              break;
            // z ≰ x  ∧  x < u implies nothing
            case PoComp::LESS:
            // z ≰ x  ∧  x ≱ u implies nothing
            case PoComp::NGEQ:
            // z ≰ x  ∧  x ≰ u implies nothing
            case PoComp::NLEQ:
            // z ≰ x  ∧  x ⋈ u implies nothing
            case PoComp::INCOMPARABLE:
              break;
            default:
              ASSERTION_VIOLATION;
          }
        }
        break;
      }
      default:
        ASSERTION_VIOLATION;
    }
  }
  return true;
}

bool PartialOrdering::set_inferred(size_t x, size_t y, PoComp result)
{
  switch (result) {
    /* x > y: then ∀z. y ≥ z, also x > z,
               and ∀z. z ≥ x, also z > y */
    case PoComp::GREATER:
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case PoComp::LESS:
      RETURN_IF_FAIL(set_inferred_loop(x, y, result));
      break;
    /* x = y: then ∀z. z = x, also z = y
               and ∀z. z = y, also z = x
               and ∀z. z > x, also z > y
               and ∀z. z > y, also z > x
               and ∀z. z < x, also z < y
               and ∀z. z < y, also z < x */
    case PoComp::EQUAL:
      RETURN_IF_FAIL(set_inferred_loop_eq(x, y));
      break;
    case PoComp::NGEQ:
    case PoComp::NLEQ:
      RETURN_IF_FAIL(set_inferred_loop_inc(x, y, result));
      break;
    case PoComp::INCOMPARABLE:
      RETURN_IF_FAIL(set_inferred_loop_inc(x, y, PoComp::NGEQ));
      RETURN_IF_FAIL(set_inferred_loop_inc(x, y, PoComp::NLEQ));
      break;
    default:
      break;
  }
  return true;
}

string idx_to_string(PoComp c) {
  switch (c) {
    case PoComp::UNKNOWN:
      return "UNKNOWN";
    case PoComp::GREATER:
      return "GREATER";
    case PoComp::EQUAL:
      return "EQUAL";
    case PoComp::LESS:
      return "LESS";
    case PoComp::NGEQ:
      return "NGEQ";
    case PoComp::NLEQ:
      return "NLEQ";
    case PoComp::INCOMPARABLE:
      return "INCOMPARABLE";
  }
}

string idx_to_infix(PoComp c) {
  switch (c) {
    case PoComp::UNKNOWN:
      return "?";
    case PoComp::GREATER:
      return ">";
    case PoComp::EQUAL:
      return "=";
    case PoComp::LESS:
      return "<";
    case PoComp::NGEQ:
      return "≱";
    case PoComp::NLEQ:
      return "≰";
    case PoComp::INCOMPARABLE:
      return "⋈";
  }
}

string PartialOrdering::to_string() const
{
  if (_nodes.size()<2) {
    return " {} ";
  }
  stringstream str;
  typename Map<TermList,size_t>::Iterator it(_nodes);
  while (it.hasNext()) {
    const auto& e = it.next();
    str << e.value() << ": " << e.key() << ", ";
  }
  str << endl;

  size_t s = _size-1;
  size_t w = 0;
  while (s) { s /= 10; w++; }

  for (size_t i = 0; i < _size; i++) {
    str << std::setw(w) << i << " ";
    for (size_t j = 0; j < i; j++) {
      if (w>1) {
        str << std::setw(w-1) << " ";
      }
      str << idx_to_infix(idx_of(j,i)) << " ";
    }
    if (w>1) {
      str << std::setw(w-1) << " ";
    }
    str << idx_to_infix(PoComp::EQUAL) << " " << endl;
  }
  str << std::setw(w) << " " << " ";
  for (size_t i = 0; i < _size; i++) {
    str << std::setw(w) << i << " ";
  }
  return str.str();
}

string PartialOrdering::all_to_string() const
{
  stringstream res;
  auto curr = this;
  while (curr) {
    res << curr << " " << curr->_array << endl;
    res << curr->to_string() << endl;
    curr = curr->_prev;
  }
  return res.str();
}

#if DEBUG_ORDERING
void PartialOrdering::debug_check() const
{
  auto output_args = [this](size_t x, size_t y, size_t z) {
    return all_to_string() + " at " + Int::toString(x) + ", " + Int::toString(y) + ", " + Int::toString(z);
  };

  auto check_val = [&output_args](auto actual_val, auto expected_val, size_t x, size_t y, size_t z) {
    if (actual_val == PoComp::UNKNOWN) {
      INVALID_OPERATION(output_args(x,y,z));
    }
    if (expected_val == PoComp::NLEQ) {
      if (actual_val != PoComp::NLEQ && actual_val != PoComp::INCOMPARABLE && actual_val != PoComp::GREATER) {
        INVALID_OPERATION(output_args(x,y,z));
      }
    } else if (expected_val == PoComp::NGEQ) {
      if (actual_val != PoComp::NGEQ && actual_val != PoComp::INCOMPARABLE && actual_val != PoComp::LESS) {
        INVALID_OPERATION(output_args(x,y,z));
      }
    } else {
      if (actual_val != expected_val) {
        INVALID_OPERATION(output_args(x,y,z));
      }
    }
  };

  decltype(_nodes)::Iterator it1(_nodes);
  while (it1.hasNext()) {
    auto& e1 = it1.next();

    decltype(_nodes)::Iterator it2(_nodes);
    while (it2.hasNext()) {
      auto& e2 = it2.next();
      if (e1.value() == e2.value()) {
        continue;
      }
      auto v12 = idx_of_safe(e1.value(),e2.value());
      if (v12 == PoComp::UNKNOWN) {
        continue;
      }
      auto comp = _ord.compare(e1.key(),e2.key());
      if (comp != Ordering::INCOMPARABLE) {
        check_val(v12, resultToPoComp(comp, false), e1.value(), e2.value(), e2.value());
      }

      decltype(_nodes)::Iterator it3(_nodes);
      while (it3.hasNext()) {
        auto& e3 = it3.next();
        if (e1.value() == e3.value() || e2.value() == e3.value()) {
          continue;
        }

        auto v13 = idx_of_safe(e1.value(),e3.value());
        if (v13 == PoComp::UNKNOWN) {
          continue;
        }

        auto v23 = idx_of_safe(e2.value(),e3.value());

        switch (v12) {
          case PoComp::UNKNOWN:
            break;
          case PoComp::EQUAL:
            // x = y rel z -> x rel z
            check_val(v13, v23, e1.value(), e2.value(), e3.value());
            break;
          case PoComp::GREATER:
          case PoComp::NLEQ: {
            if (v23 == PoComp::EQUAL || v23 == PoComp::GREATER) {
              // x > y ≥ z -> x > z
              // x ≰ y ≥ z -> x ≰ z
              check_val(v13, v12, e1.value(), e2.value(), e3.value());
            }
            break;
          }
          case PoComp::LESS:
          case PoComp::NGEQ: {
            if (v23 == PoComp::EQUAL || v23 == PoComp::LESS) {
              // x < y ≤ z -> x < z
              // x ≱ y ≤ z -> x ≱ z
              check_val(v13, v12, e1.value(), e2.value(), e3.value());
            }
            break;
          }
          case PoComp::INCOMPARABLE: {
            if (v23 == PoComp::EQUAL || v23 == PoComp::GREATER) {
              // x ≰ y ≥ z -> x ≰ z
              check_val(v13, PoComp::NLEQ, e1.value(), e2.value(), e3.value());
            }
            if (v23 == PoComp::EQUAL || v23 == PoComp::LESS) {
              // x ≱ y ≤ z -> x ≱ z
              check_val(v13, PoComp::NGEQ, e1.value(), e2.value(), e3.value());
            }
            break;
          }
        }
      }
    }
  }
}
#endif

}
