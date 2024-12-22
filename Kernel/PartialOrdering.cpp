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
  ASSERTION_VIOLATION;
}

constexpr PoComp weaken(PoComp v) {
  switch (v) {
    case PoComp::GREATER:
      return PoComp::NLEQ;
    case PoComp::LESS:
      return PoComp::NGEQ;
    default:
      break;
  }
  ASSERTION_VIOLATION;
}

constexpr PoComp strengthen(PoComp v) {
  switch (v) {
    case PoComp::NLEQ:
      return PoComp::GREATER;
    case PoComp::NGEQ:
      return PoComp::LESS;
    default:
      break;
  }
  ASSERTION_VIOLATION;
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
      break;
  }
  ASSERTION_VIOLATION;
}

string pocompToInfix(PoComp c) {
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
  ASSERTION_VIOLATION;
}

PartialOrdering::PartialOrdering()
  : _size(0), _array(nullptr) {}

PartialOrdering::PartialOrdering(const PartialOrdering& other)
  : _size(other._size), _array(nullptr)
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

PoComp PartialOrdering::get(size_t x, size_t y) const
{
  ASS_L(x,_size);
  ASS_L(y,_size);

  return (x < y) ? getUnsafe(x,y) : reverse(getUnsafe(y,x));
}

const PartialOrdering* PartialOrdering::getEmpty()
{
  static PartialOrdering empty;
  return &empty;
}

const PartialOrdering* PartialOrdering::set(const PartialOrdering* po, size_t x, size_t y, PoComp v)
{
  ASS(po);
  ASS_L(x,po->_size);
  ASS_L(y,po->_size);

  if (x == y) {
    return po;
  }

  static DHMap<std::tuple<const PartialOrdering*, size_t, size_t, PoComp>, const PartialOrdering*> cache;

  const PartialOrdering** ptr;
  if (cache.getValuePtr(make_tuple(po, x, y, v), ptr, nullptr)) {
    // TODO remove this reverse thing
    bool reversed = x > y;
    if (reversed) {
      swap(x,y);
    }
    auto res = new PartialOrdering(*po);
    bool changed;
    if (!res->setRel(x, y, v, changed)) {
      delete res;
      *ptr = nullptr;
    } else if (!changed) {
      delete res;
      *ptr = po;
    }
    // if something's changed, we calculate the transitive closure
    // TODO we could use the value that we get from compatibility checking here
    else if (!res->setInferred(x, y, v)) {
      delete res;
      *ptr = nullptr;
    } else {
      *ptr = res;
    }
  }
  return *ptr;
}

const PartialOrdering* PartialOrdering::extend(const PartialOrdering* po)
{
  static DHMap<const PartialOrdering*, const PartialOrdering*> cache;

  const PartialOrdering** ptr;
  if (cache.getValuePtr(po, ptr, nullptr)) {
    auto res = new PartialOrdering(*po);
    res->extend();
    *ptr = res;
  }
  return *ptr;
}

void PartialOrdering::extend()
{
  // extend array
  size_t prevSize = ((_size - 1) * _size / 2);
  auto prevArray = _array;
  _size++;
  if (_size>1) {
    size_t newSize = prevSize + _size;
    void* mem = ALLOC_KNOWN(newSize*sizeof(PoComp), "Kernel::PartialOrdering");
    _array = array_new<PoComp>(mem, newSize);
    std::memset(_array, 0, newSize*sizeof(PoComp));
    static_assert(static_cast<unsigned>(PoComp::UNKNOWN) == 0);
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

bool PartialOrdering::setRel(size_t x, size_t y, PoComp v, bool& changed)
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
  return true;
}

bool PartialOrdering::setRelSafe(size_t x, size_t y, PoComp v, bool& changed)
{
  if (x < y) {
    return setRel(x,y,v,changed);
  } else {
    return setRel(y,x,reverse(v),changed);
  }
}

PoComp PartialOrdering::getUnsafe(size_t x, size_t y) const
{
  size_t idx = y*(y-1)/2 + x;
  ASS_L(idx,((_size - 1) * _size / 2));
  return _array[idx];
}

bool PartialOrdering::setInferred(size_t x, size_t y, PoComp result)
{
  switch (result) {
    /* x > y: then ∀z. y ≥ z, also x > z,
               and ∀z. z ≥ x, also z > y */
    case PoComp::GREATER:
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case PoComp::LESS:
      RETURN_IF_FAIL(setInferredHelper(x, y, result));
      break;
    /* x = y: then ∀z. z = x, also z = y
               and ∀z. z = y, also z = x
               and ∀z. z > x, also z > y
               and ∀z. z > y, also z > x
               and ∀z. z < x, also z < y
               and ∀z. z < y, also z < x */
    case PoComp::EQUAL:
      RETURN_IF_FAIL(setInferredHelperEq(x, y));
      break;
    case PoComp::NGEQ:
    case PoComp::NLEQ:
      RETURN_IF_FAIL(setInferredHelperInc(x, y, result));
      break;
    case PoComp::INCOMPARABLE:
      RETURN_IF_FAIL(setInferredHelperInc(x, y, PoComp::NGEQ));
      RETURN_IF_FAIL(setInferredHelperInc(x, y, PoComp::NLEQ));
      break;
    default:
      break;
  }
  return true;
}

bool PartialOrdering::setInferredHelper(size_t x, size_t y, PoComp rel)
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
    auto r = get(z, x);
    // if rel = ≤: z ≤ x  ∧  x ≤ y  →  z ≤ y
    // if rel = ≥: z ≥ x  ∧  x ≥ y  →  z ≥ y
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(setRelSafe(z, y, rel, changed));
      if (changed) {
        above.push(z);
        // TODO find out why we should continue here
        // continue;
      }
    }
    // if rel = ≤: z ≱ x  ∧  x ≤ y  →  z ≱ y
    // if rel = ≥: z ≰ x  ∧  x ≥ y  →  z ≰ y
    else if (r == wkn || r == PoComp::INCOMPARABLE) {
      RETURN_IF_FAIL(setRelSafe(z, y, wkn, changed));
      if (changed) {
        above_w.push(z);
        // TODO find out why we should continue here
        // continue;
      }
    }

    r = get(y, z);
    // x rel y  ∧  y rel z  →  x rel z
    // x rel y  ∧  y  =  z  →  x rel z
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(setRelSafe(x, z, rel, changed));
      if (changed) {
        below.push(z);
      }
    }
    // x rel y  ∧  y wkn z  →  x wkn z
    // x rel y  ∧  y inc z  →  x wkn z
    else if (r == wkn || r == PoComp::INCOMPARABLE) {
      RETURN_IF_FAIL(setRelSafe(x, z, wkn, changed));
      if (changed) {
        below_w.push(z);
      }
    }
  }

  // connect all pairs that have been derived
  for (const auto& z : above) {
    for (const auto& u : below) {
      RETURN_IF_FAIL(setRelSafe(z,u,rel,changed));
    }
    for (const auto& u : below_w) {
      RETURN_IF_FAIL(setRelSafe(z,u,wkn,changed));
    }
  }
  for (const auto& z : above_w) {
    for (const auto& u : below) {
      RETURN_IF_FAIL(setRelSafe(z,u,wkn,changed));
    }
  }
  return true;
}

bool PartialOrdering::setInferredHelperInc(size_t x, size_t y, PoComp wkn)
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
    auto r = get(z, x);
    // z ≤ x  ∧  x ≱ y  →  z ≱ y
    // z ≥ x  ∧  x ≰ y  →  z ≰ y
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(setRelSafe(z, y, wkn, changed));
      if (changed) {
        above.push(z);
        // TODO find out why we should continue here
        // continue;
      }
    }
    r = get(y, z);
    // x ≱ y  ∧  y ≤ z  →  x ≱ z
    // x ≰ y  ∧  y ≥ z  →  x ≰ z
    if (r == rel || r == PoComp::EQUAL) {
      RETURN_IF_FAIL(setRelSafe(x, z, wkn, changed));
      if (changed) {
        below.push(z);
      }
    }
  }

  // connect all pairs that have been derived
  for (const auto& z : above) {
    for (const auto& u : below) {
      RETURN_IF_FAIL(setRelSafe(z,u,wkn,changed));
    }
  }
  return true;
}

bool PartialOrdering::setInferredHelperEq(size_t x, size_t y)
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
    auto r = get(z, x);
    if (r != PoComp::UNKNOWN) {
      RETURN_IF_FAIL(setRelSafe(z, y, r, changed));
      if (changed) {
        x_rel.push({ z, r });
        // TODO find out why we should continue here
        // continue;
      }
    }
    r = get(y, z);
    if (r != PoComp::UNKNOWN) {
      RETURN_IF_FAIL(setRelSafe(x, z, r, changed));
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
          RETURN_IF_FAIL(setRelSafe(z, u, ru, changed));
        }
        break;
      }
      case PoComp::GREATER: {
        for (const auto& [u,ru] : y_rel) {
          switch (ru) {
            // z > x  ∧  x ≥ u  →  z > u
            case PoComp::EQUAL:
            case PoComp::GREATER:
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::GREATER, changed));
              break;
            // z > x  ∧  x ≰ u  →  z ≰ u
            case PoComp::NLEQ:
            case PoComp::INCOMPARABLE:
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::NLEQ, changed));
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
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::LESS, changed));
              break;
            // z < x  ∧  x ≱ u  →  z ≱ u
            case PoComp::NGEQ:
            case PoComp::INCOMPARABLE:
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::NGEQ, changed));
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
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::NLEQ, changed));
              break;
            // z ⋈ x  ∧  x = u  →  z ⋈ u
            case PoComp::EQUAL:
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::INCOMPARABLE, changed));
              break;
            // z ≱ x  ∧  x < u  →  z ≱ u
            case PoComp::LESS:
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::NGEQ, changed));
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
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::NGEQ, changed));
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
              RETURN_IF_FAIL(setRelSafe(z, u, PoComp::NLEQ, changed));
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

ostream& operator<<(ostream& str, const PartialOrdering& po)
{
  if (po._size == 0) {
    return str << " {} ";
  }
  size_t s = po._size-1;
  size_t w = 0;
  while (s) { s /= 10; w++; }

  for (size_t i = 0; i < po._size; i++) {
    str << std::setw(w) << i << " ";
    for (size_t j = 0; j < i; j++) {
      if (w>1) {
        str << std::setw(w-1) << " ";
      }
      str << pocompToInfix(po.getUnsafe(j,i)) << " ";
    }
    if (w>1) {
      str << std::setw(w-1) << " ";
    }
    str << pocompToInfix(PoComp::EQUAL) << " " << endl;
  }
  str << std::setw(w) << " " << " ";
  for (size_t i = 0; i < po._size; i++) {
    str << std::setw(w) << i << " ";
  }
  return str;
}

}