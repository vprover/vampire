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

PartialOrdering::PartialOrdering()
  : _nodes(), _size(0), _array(nullptr), _hasIncomp(false) {}

PartialOrdering::PartialOrdering(const PartialOrdering& other)
  : _nodes(other._nodes), _size(_nodes.size()), _array(nullptr), _hasIncomp(other._hasIncomp)
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

bool PartialOrdering::get(TermList lhs, TermList rhs, Result& res) const
{
  if (lhs == rhs) {
    res = Result::EQUAL;
    return true;
  }
  if (!_nodes.find(lhs) || !_nodes.find(rhs)) {
    return false;
  }
  size_t x = idx_of_elem(lhs);
  size_t y = idx_of_elem(rhs);
  bool reversed = x > y;
  if (reversed) {
    swap(x,y);
  }
  PoComp val = idx_of(x,y);
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
  PoComp old_val = idx_of(x, y);
  PoComp new_val = resultToPoComp(con.rel, reversed);
  if (set_idx_of(x, y, new_val)) {
    // if something's changed, we calculate the transitive closure
    if (new_val != old_val) {
      set_inferred(x, y, new_val);
    }
    return true;
  }
  return false;
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
  }
  return *ptr;
}

bool PartialOrdering::set_idx_of(size_t x, size_t y, PoComp v)
{
  size_t idx = y*(y-1)/2 + x;
  ASS_L(idx,((_size - 1) * _size / 2));
  PoComp new_v;
  if (!checkCompatibility(_array[idx], v, new_v)) {
    return false;
  }
  _array[idx] = new_v;
  if (new_v == PoComp::INCOMPARABLE) {
    _hasIncomp = true;
  }
  return true;
}

bool PartialOrdering::set_idx_of_safe(size_t x, size_t y, PoComp v)
{
  if (x < y) {
    return set_idx_of(x,y,v);
  } else {
    return set_idx_of(y,x,reverse(v));
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

void PartialOrdering::set_inferred_loop(size_t x, size_t y, PoComp rel)
{
  ASS_NEQ(x,y);

  Stack<size_t> above;
  Stack<size_t> above_w;
  Stack<size_t> below;
  Stack<size_t> below_w;
  auto wkn = weaken(rel); // weakened variant of rel
  for (size_t z = 0; z < _size; z++) {
    if (z == x || z == y) {
      continue;
    }
    auto r = idx_of_safe(z, x);
    // if rel = ≤: z ≤ x  ∧  x ≤ y  →  z ≤ y
    // if rel = ≥: z ≥ x  ∧  x ≥ y  →  z ≥ y
    if (r == rel || r == PoComp::EQUAL) {
      ALWAYS(set_idx_of_safe(z, y, rel));
      above.push(z);
      continue;
    }
    // if rel = ≤: z ≱ x  ∧  x ≤ y  →  z ≱ y
    // if rel = ≥: z ≰ x  ∧  x ≥ y  →  z ≰ y
    if (r == wkn || r == PoComp::INCOMPARABLE) {
      ALWAYS(set_idx_of_safe(z, y, wkn));
      above_w.push(z);
      continue;
    }
    r = idx_of_safe(y, z);
    // x rel y  ∧  y rel z  →  x rel z
    // x rel y  ∧  y  =  z  →  x rel z
    if (r == rel || r == PoComp::EQUAL) {
      ALWAYS(set_idx_of_safe(x, z, rel));
      below.push(z);
      continue;
    }
    // x rel y  ∧  y wkn z  →  x wkn z
    // x rel y  ∧  y inc z  →  x wkn z
    if (r == wkn || r == PoComp::INCOMPARABLE) {
      ALWAYS(set_idx_of_safe(x, z, wkn));
      below_w.push(z);
      continue;
    }
  }

  // connect all pairs that have been derived
  for (const auto& z : above) {
    for (const auto& u : below) {
      ALWAYS(set_idx_of_safe(z,u,rel));
    }
    for (const auto& u : below_w) {
      ALWAYS(set_idx_of_safe(z,u,wkn));
    }
  }
  for (const auto& z : above_w) {
    for (const auto& u : below) {
      ALWAYS(set_idx_of_safe(z,u,wkn));
    }
  }
}

void PartialOrdering::set_inferred_loop_inc(size_t x, size_t y, PoComp wkn)
{
  ASS_NEQ(x,y);

  Stack<size_t> above;
  Stack<size_t> below;
  auto rel = strengthen(wkn); // stronger variant of wkn

  for (size_t z = 0; z < _size; z++) {
    if (z == x || z == y) {
      continue;
    }
    auto r = idx_of_safe(z, x);
    // z ≤ x  ∧  x ≱ y  →  z ≱ y
    if (r == rel || r == PoComp::EQUAL) {
      ALWAYS(set_idx_of_safe(z, y, wkn));
      above.push(z);
      continue;
    }
    r = idx_of_safe(y, z);
    // x ≱ y  ∧  y ≤ z  →  x ≱ z
    if (r == rel || r == PoComp::EQUAL) {
      ALWAYS(set_idx_of_safe(x, z, wkn));
      below.push(z);
      continue;
    }
  }

  // connect all pairs that have been derived
  for (const auto& z : above) {
    for (const auto& u : below) {
      ALWAYS(set_idx_of_safe(z,u,wkn));
    }
  }
}

void PartialOrdering::set_inferred_loop_eq(size_t x, size_t y)
{
  ASS_NEQ(x,y);

  // pairs (z, rel) s.t. z rel x
  Stack<pair<size_t,PoComp>> x_rel;
  // pairs (z, rel) s.t. y rel z
  Stack<pair<size_t,PoComp>> y_rel;

  for (size_t z = 0; z < _size; z++) {
    if (z == x || z == y) {
      continue;
    }
    auto r = idx_of_safe(z, x);
    if (r != PoComp::UNKNOWN) {
      ALWAYS(set_idx_of_safe(z, y, r));
      x_rel.push({ z, r });
      continue;
    }
    r = idx_of_safe(y, z);
    if (r != PoComp::UNKNOWN) {
      ALWAYS(set_idx_of_safe(x, z, r));
      y_rel.push({ z, r });
    }
  }

  if (y_rel.isEmpty()) {
    return;
  }

  // we assume x = y
  for (const auto& [z,rz] : x_rel) {
    switch (rz) {
      case PoComp::EQUAL: {
        for (const auto& [u,ru] : y_rel) {
          // z = x  ∧  x ru u  →  z ru u
          ALWAYS(set_idx_of_safe(z, u, ru));
        }
        break;
      }
      case PoComp::GREATER: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z > x  ∧  x ≥ u  →  z > u
            case PoComp::EQUAL:
            case PoComp::GREATER:
              ALWAYS(set_idx_of_safe(z, u, PoComp::GREATER));
              break;
            // z > x  ∧  x ≰ u  →  z ≰ u
            case PoComp::NLEQ:
            case PoComp::INCOMPARABLE:
              ALWAYS(set_idx_of_safe(z, u, PoComp::NLEQ));
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
              ALWAYS(set_idx_of_safe(z, u, PoComp::LESS));
              break;
            // z < x  ∧  x ≱ u  →  z ≱ u
            case PoComp::NGEQ:
            case PoComp::INCOMPARABLE:
              ALWAYS(set_idx_of_safe(z, u, PoComp::NGEQ));
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
              ALWAYS(set_idx_of_safe(z, u, PoComp::NLEQ));
              break;
            // z ⋈ x  ∧  x = u  →  z ⋈ u
            case PoComp::EQUAL:
              ALWAYS(set_idx_of_safe(z, u, PoComp::INCOMPARABLE));
              break;
            // z ≱ x  ∧  x < u  →  z ≱ u
            case PoComp::LESS:
              ALWAYS(set_idx_of_safe(z, u, PoComp::NGEQ));
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
              ALWAYS(set_idx_of_safe(z, u, PoComp::NGEQ));
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
              ALWAYS(set_idx_of_safe(z, u, PoComp::NLEQ));
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
}

void PartialOrdering::set_inferred(size_t x, size_t y, PoComp result)
{
  switch (result) {
    /* x > y: then ∀z. y ≥ z, also x > z,
               and ∀z. z ≥ x, also z > y */
    case PoComp::GREATER:
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case PoComp::LESS:
      set_inferred_loop(x, y, result);
      break;
    /* x = y: then ∀z. z = x, also z = y
               and ∀z. z = y, also z = x
               and ∀z. z > x, also z > y
               and ∀z. z > y, also z > x
               and ∀z. z < x, also z < y
               and ∀z. z < y, also z < x */
    case PoComp::EQUAL:
      set_inferred_loop_eq(x, y);
      break;
    case PoComp::NGEQ:
    case PoComp::NLEQ:
      set_inferred_loop_inc(x, y, result);
      break;
    case PoComp::INCOMPARABLE:
      set_inferred_loop_inc(x, y, PoComp::NGEQ);
      set_inferred_loop_inc(x, y, PoComp::NLEQ);
      break;
    default:
      break;
  }
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

}
