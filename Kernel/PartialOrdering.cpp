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
    case PoComp::LTR_INCOMPARABLE:
      return PoComp::RTL_INCOMPARABLE;
    case PoComp::RTL_INCOMPARABLE:
      return PoComp::LTR_INCOMPARABLE;
    case PoComp::INCOMPARABLE:
      return PoComp::INCOMPARABLE;
  }
}

Result poCompToResult(PoComp c) {
  switch (c) {
    case PoComp::UNKNOWN:
      ASSERTION_VIOLATION;
    case PoComp::GREATER:
      return Result::GREATER;
    case PoComp::EQUAL:
      return Result::EQUAL;
    case PoComp::LESS:
      return Result::LESS;
    case PoComp::LTR_INCOMPARABLE:
    case PoComp::RTL_INCOMPARABLE:
    case PoComp::INCOMPARABLE:
      return Result::INCOMPARABLE;
  }
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
      return reversed ? PoComp::RTL_INCOMPARABLE : PoComp::LTR_INCOMPARABLE;
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
    case PoComp::LTR_INCOMPARABLE:
      return "LTR_INCOMPARABLE";
    case PoComp::RTL_INCOMPARABLE:
      return "RTL_INCOMPARABLE";
    case PoComp::INCOMPARABLE:
      return "INCOMPARABLE";
  }
}

PartialOrdering::PartialOrdering()
  : _nodes(), _inverse(), _size(0), _array(nullptr) {}

PartialOrdering::PartialOrdering(const PartialOrdering& other)
  : _nodes(other._nodes), _inverse(other._inverse), _size(_nodes.size()), _array(nullptr)
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

void PartialOrdering::reset()
{
  std::memset(_array, 0, ((_size - 1) * _size / 2)*sizeof(PoComp));
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
    if (val == PoComp::LTR_INCOMPARABLE) {
      return false;
    }
    res = Ordering::reverse(poCompToResult(val));
    return true;
  } else {
    if (val == PoComp::RTL_INCOMPARABLE) {
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
      return old == PoComp::GREATER || old == PoComp::RTL_INCOMPARABLE;
    case PoComp::EQUAL:
      res = PoComp::EQUAL;
      return old == PoComp::EQUAL;
    case PoComp::LESS:
      res = PoComp::LESS;
      return old == PoComp::LESS || old == PoComp::LTR_INCOMPARABLE;
    case PoComp::INCOMPARABLE:
      res = PoComp::INCOMPARABLE;
      return old == PoComp::INCOMPARABLE || old == PoComp::LTR_INCOMPARABLE || old == PoComp::RTL_INCOMPARABLE;
    case PoComp::LTR_INCOMPARABLE:
      switch (old) {
        case PoComp::LESS:
        case PoComp::INCOMPARABLE:
        case PoComp::LTR_INCOMPARABLE:
          res = old;
          return true;
        case PoComp::RTL_INCOMPARABLE:
          res = PoComp::INCOMPARABLE;
          return true;
        default:
          return false;
      }
      break;
    case PoComp::RTL_INCOMPARABLE:
      switch (old) {
        case PoComp::GREATER:
        case PoComp::INCOMPARABLE:
        case PoComp::RTL_INCOMPARABLE:
          res = old;
          return true;
        case PoComp::LTR_INCOMPARABLE:
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
  PoComp curr = resultToPoComp(con.rel, reversed);
  PoComp old = idx_of(x,y);
  PoComp res;
  if (checkCompatibility(old, curr, res)) {
    set_idx_of(x,y,res);
    // if something's changed, we calculate the transitive closure
    if (curr != res) {
      set_inferred(x,y,res);
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
    ALWAYS(_inverse.insert(_size, t));
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

void PartialOrdering::set_idx_of(size_t x, size_t y, PoComp v)
{
  size_t idx = y*(y-1)/2 + x;
  ASS_L(idx,((_size - 1) * _size / 2));
  _array[idx] = v;
}

void PartialOrdering::set_idx_of_safe(size_t x, size_t y, PoComp v)
{
  if (x < y) {
    set_idx_of(x,y,v);
  } else {
    set_idx_of(y,x,v);
  }
}

PoComp PartialOrdering::idx_of(size_t x, size_t y) const
{
  size_t idx = y*(y-1)/2 + x;
  ASS_L(idx,((_size - 1) * _size / 2));
  return _array[idx];
}

void PartialOrdering::set_inferred_loop(size_t x, size_t y, PoComp rel)
{
  ASS_NEQ(x,y);

  Stack<size_t> above;
  Stack<size_t> below;
  bool sort = x < y;
  size_t min = sort ? x : y;
  size_t max = sort ? y : x;
  auto inv = reverse(rel); // inverse of rel

  // z<x z<y
  for (size_t z = 0; z < min; z++) {
    auto r = idx_of(z, x);
    // z rel x /\ x rel y -> z rel y
    // z  =  x /\ x rel y -> z rel y
    if (r == rel || r == PoComp::EQUAL) {
      set_idx_of(z, y, rel);
      above.push(z);
      continue;
    }
    r = idx_of(z, y);
    // x rel y /\ y rel z -> x rel z
    // x rel y /\ y  =  z -> x rel z
    if (r == inv || r == PoComp::EQUAL) {
      set_idx_of(z, x, inv);
      below.push(z);
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z = min + 1; z < max; z++) {
      auto r = idx_of(x, z);
      // z rel x /\ x rel y -> z rel y
      // z  =  x /\ x rel y -> z rel y
      if (r == inv || r == PoComp::EQUAL) {
        set_idx_of(z, y, rel);
        above.push(z);
        continue;
      }
      r = idx_of(z, y);
      // x rel y /\ y rel z -> x rel z
      // x rel y /\ y  =  z -> x rel z
      if (r == inv || r == PoComp::EQUAL) {
        set_idx_of(x, z, rel);
        below.push(z);
      }
    }
  } else {
    // y<z<x
    for (size_t z = min + 1; z < max; z++) {
      auto r = idx_of(z, x);
      // z rel x /\ x rel y -> z rel y
      // z  =  x /\ x rel y -> z rel y
      if (r == rel || r == PoComp::EQUAL) {
        set_idx_of(y, z, inv);
        above.push(z);
        continue;
      }
      r = idx_of(y, z);
      // x rel y /\ y rel z -> x rel z
      // x rel y /\ y  =  z -> x rel z
      if (r == rel || r == PoComp::EQUAL) {
        set_idx_of(z, x, inv);
        below.push(z);
      }
    }
  }

  // x<z y<z
  for (size_t z = max + 1; z < _size; z++) {
    auto r = idx_of(x, z);
    // z rel x /\ x rel y -> z rel y
    // z  =  x /\ x rel y -> z rel y
    if (r == inv || r == PoComp::EQUAL) {
      set_idx_of(y, z, inv);
      above.push(z);
      continue;
    }
    r = idx_of(y, z);
    // x rel y /\ y rel z -> x rel z
    // x rel y /\ y  =  z -> x rel z
    if (r == rel || r == PoComp::EQUAL) {
      set_idx_of(x, z, rel);
      below.push(z);
    }
  }

  // connect all pairs that have been derived
  for (const auto& x : above) {
    for (const auto& y : below) {
      set_idx_of_safe(x,y,rel);
    }
  }
}

void PartialOrdering::set_inferred_loop_eq(size_t x, size_t y)
{
  ASS_NEQ(x,y);

  Stack<pair<size_t,PoComp>> above;
  Stack<pair<size_t,PoComp>> below;

  bool sort = x < y;
  size_t min = sort ? x : y;
  size_t max = sort ? y : x;

  // z<x z<y
  for (size_t z = 0; z < min; z++) {
    auto r = idx_of(z, x);
    if (/* r != none && */r != PoComp::INCOMPARABLE) {  // TODO wouldn't INC be propagated too?
      set_idx_of(z, y, r);
      above.push(make_pair(z,r));
      continue;
    }
    r = idx_of(z, y);
    if (/* r != none && */r != PoComp::INCOMPARABLE) {
      set_idx_of(z, x, r);
      below.push(make_pair(z,r));
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z = min + 1; z < max; z++) {
      auto r = idx_of(x, z);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(z, y, reverse(r));
        above.push(make_pair(z,reverse(r)));
        continue;
      }
      r = idx_of(z, y);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(x, z, reverse(r));
        below.push(make_pair(z,r));
      }
    }
  } else {
    // y<z<x
    for (size_t z = min + 1; z < max; z++) {
      auto r = idx_of(z, x);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(y, z, reverse(r));
        above.push(make_pair(z,r));
        continue;
      }
      r = idx_of(y, z);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(z, x, reverse(r));
        below.push(make_pair(z,reverse(r)));
      }
    }
  }

  // x<z y<z
  for (size_t z = max + 1; z < _size; z++) {
    auto r = idx_of(x, z);
    if (/* r != none && */r != PoComp::INCOMPARABLE) {
      set_idx_of(y, z, r);
      above.push(make_pair(z,reverse(r)));
      continue;
    }
    r = idx_of(y, z);
    if (/* r != none && */r != PoComp::INCOMPARABLE) {
      set_idx_of(x, z, r);
      below.push(make_pair(z,reverse(r)));
    }
  }

  if (below.isNonEmpty()) {
    for (const auto& [x,rx] : above) {
      switch (rx) {
        case PoComp::EQUAL: {
          for (const auto& [y,ry] : below) {
            set_idx_of_safe(y, x, ry);
          }
          break;
        }
        case PoComp::GREATER: {
          for (const auto& [y,ry] : below) {
            switch (ry) {
              case PoComp::GREATER:
                break;
              case PoComp::EQUAL:
              case PoComp::LESS:
                set_idx_of_safe(x,y,PoComp::GREATER);
                break;
              default:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case PoComp::LESS: {
          for (const auto& [y,ry] : below) {
            switch (ry) {
              case PoComp::LESS:
                break;
              case PoComp::EQUAL:
              case PoComp::GREATER:
                set_idx_of_safe(x,y,PoComp::LESS);
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
}

void PartialOrdering::set_inferred(size_t x, size_t y, PoComp result)
{
  switch (result) {
    /* x > y: then ∀z. y ≥ z, also x > z,
               and ∀z. z ≥ x, also z > y */
    case PoComp::GREATER:
      set_inferred_loop(x, y, PoComp::GREATER);
      break;
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case PoComp::LESS:
      set_inferred_loop(x, y, PoComp::LESS);
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
    /* if INC then nothing can be inferred */
    default:
      break;
  }
}

string PartialOrdering::to_string() const
{
  if (_nodes.size()<2) {
    return "{}";
  }
  stringstream str;
  typename DHMap<TermList,size_t>::Iterator vit1(_nodes);
  while (vit1.hasNext()) {
    TermList t1;
    size_t v1;
    vit1.next(t1,v1);
    typename DHMap<TermList,size_t>::Iterator vit2(_nodes);
    while (vit2.hasNext()) {
      TermList t2;
      size_t v2;
      vit2.next(t2,v2);
      if (v1 < v2) {
        auto c = idx_of(v1,v2);
        if (c == PoComp::UNKNOWN) {
          continue;
        }
        str << " { " << t1 << " " << t2 << " " << idx_to_string(c) << " }, " << endl;
      }
    }
  }
  return str.str();
}

}
