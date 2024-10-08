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

uint8_t reverseSafe(uint8_t v) {
  if (!v) {
    return v;
  }
  ASS_LE(v,Ordering::INCOMPARABLE);
  return Ordering::reverse(Result(v));
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

// PartialOrdering& PartialOrdering::operator=(const PartialOrdering& other)
// {
//   auto prevSize = ((_size - 1) * _size / 2);
//   if (prevSize) {
//     array_delete(_array, prevSize);
//     DEALLOC_KNOWN(_array, prevSize*sizeof(PoComp), "Kernel::PartialOrdering");
//   }
//   _nodes = other._nodes;
//   _nodes.reset();
//   _nodes.loadFromMap(other._nodes);
//   _inverse.reset();
//   _inverse.loadFromMap(other._inverse);
//   _size = other._size;
//   size_t arrSize = ((_size - 1) * _size / 2);
//   if (arrSize) {
//     void* mem = ALLOC_KNOWN(arrSize*sizeof(PoComp), "Kernel::PartialOrdering");
//     _array = array_new<PoComp>(mem, arrSize);
//     memcpy(_array,other._array,arrSize*sizeof(PoComp));
//   }
//   return *this;
// }

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
  size_t idx_x = idx_of_elem(lhs);
  size_t idx_y = idx_of_elem(rhs);
  bool reversed = idx_x > idx_y;
  if (reversed) {
    swap(idx_x,idx_y);
  }
  PoComp val = idx_of(idx_x,idx_y);
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
  size_t idx_x = idx_of_elem_ext(con.lhs);
  size_t idx_y = idx_of_elem_ext(con.rhs);

  bool reversed = idx_x > idx_y;
  if (reversed) {
    swap(idx_x,idx_y);
  }
  PoComp curr = resultToPoComp(con.rel, reversed);
  PoComp old = idx_of(idx_x,idx_y);
  PoComp res;
  // cout << idx_to_string(old) << " " << idx_to_string(curr);
  if (checkCompatibility(old, curr, res)) {
    // cout << " " << idx_to_string(res) << endl;
    set_idx_of(idx_x,idx_y,res);
    if ((curr == PoComp::UNKNOWN || curr == PoComp::INCOMPARABLE) &&
      (res == PoComp::GREATER || res == PoComp::EQUAL || res == PoComp::LESS))
    {
      // set_inferred(idx_x,idx_y,poCompToResult(res));
    }
    return true;
  }
  // cout << " incompatible" << endl;
  return false;
}

// TermList PartialOrdering::get_rep(TermList t) const
// {
//   const size_t* ptr = _nodes.findPtr(e);
//   if (!ptr) {
//     return e;
//   }
//   size_t idx_e = *ptr;
//   for (size_t idx_o = 0; idx_o < idx_e; idx_o++) {
//     if (idx_of(idx_o,idx_e) == Result::EQUAL) {
//       return _inverse.get(idx_o);
//     }
//   }
//   return e;
// }

size_t PartialOrdering::idx_of_elem(TermList t) const
{
  ASS(_nodes.find(t));
  return _nodes.get(t);
}

size_t PartialOrdering::idx_of_elem_ext(TermList t)
{
  size_t *ptr;
  // cout << "size " << _size << endl;
  if (_nodes.getValuePtr(t, ptr, _size)) {
    ALWAYS(_inverse.insert(_size, t));
    // cout << "extend" << endl;
    // extend array
    size_t prevSize = ((_size - 1) * _size / 2);
    auto prevArray = _array;
    _size++;
    static unsigned maxSize = 0;
    if (_size > maxSize) {
      maxSize = _size;
      cout << "max size of partial ordering " << maxSize << endl;
    }
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
  // cout << "return " << *ptr << endl;
  return *ptr;
}

void PartialOrdering::set_idx_of(size_t idx_x, size_t idx_y, PoComp v)
{
  size_t idx = idx_y*(idx_y-1)/2 + idx_x;
  ASS_L(idx,((_size - 1) * _size / 2));
  _array[idx] = v;
}

void PartialOrdering::set_idx_of_safe(size_t idx_x, size_t idx_y, Result v)
{
  if (idx_x < idx_y) {
    set_idx_of(idx_x,idx_y,resultToPoComp(v,false));
  } else {
    set_idx_of(idx_y,idx_x,resultToPoComp(v,true));
  }
}

PoComp PartialOrdering::idx_of(size_t idx_x, size_t idx_y) const
{
  size_t idx = idx_y*(idx_y-1)/2 + idx_x;
  ASS_L(idx,((_size - 1) * _size / 2));
  return _array[idx];
}

void PartialOrdering::set_inferred_loop(size_t idx_x, size_t idx_y, Result gt, Result lt)
{
  ASS_NEQ(idx_x,idx_y);

  Stack<size_t> above;
  Stack<size_t> below;
  bool sort = idx_x < idx_y;
  size_t idx_1 = sort ? idx_x : idx_y;
  size_t idx_2 = sort ? idx_y : idx_x;

  // z<x z<y
  for (size_t z_idx = 0; z_idx < idx_1; z_idx++) {
    Result r = Result(idx_of(z_idx, idx_x));
    if (r == gt || r == Result::EQUAL) {
      set_idx_of(z_idx, idx_y, resultToPoComp(gt, false));
      above.push(z_idx);
    } else {
      Result r = Result(idx_of(z_idx, idx_y));
      if (r == lt || r == Result::EQUAL) {
        set_idx_of(z_idx, idx_x, resultToPoComp(lt, false));
        below.push(z_idx);
      }
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      Result r = Result(idx_of(idx_x, z_idx));
      if (r == lt || r == Result::EQUAL) {
        set_idx_of(z_idx, idx_y, resultToPoComp(gt, false));
        above.push(z_idx);
      } else {
        Result r = Result(idx_of(z_idx, idx_y));
        if (r == lt || r == Result::EQUAL) {
          set_idx_of(idx_x, z_idx, resultToPoComp(gt, false));
          below.push(z_idx);
        }
      }
    }
  } else {
    // y<z<x
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      Result r = Result(idx_of(z_idx, idx_x));
      if (r == gt || r == Result::EQUAL) {
        set_idx_of(idx_y, z_idx, resultToPoComp(lt, false));
        above.push(z_idx);
      } else {
        Result r = Result(idx_of(idx_y, z_idx));
        if (r == gt || r == Result::EQUAL) {
          set_idx_of(z_idx, idx_x, resultToPoComp(lt, false));
          below.push(z_idx);
        }
      }
    }
  }

  // x<z y<z
  for (size_t z_idx = idx_2 + 1; z_idx < _size; z_idx++) {
    Result r = Result(idx_of(idx_x, z_idx));
    if (r == lt || r == Result::EQUAL) {
      set_idx_of(idx_y, z_idx, resultToPoComp(lt, false));
      above.push(z_idx);
    } else {
      Result r = Result(idx_of(idx_y, z_idx));
      if (r == gt || r == Result::EQUAL) {
        set_idx_of(idx_x, z_idx, resultToPoComp(gt, false));
        below.push(z_idx);
      }
    }
  }

  // cout << "after loop " << to_string() << endl;

  for (const auto& x : above) {
    for (const auto& y : below) {
      set_idx_of_safe(x,y,gt);
    }
  }
}

void PartialOrdering::set_inferred_loop_eq(size_t idx_x, size_t idx_y)
{
  ASS_NEQ(idx_x,idx_y);

  Stack<pair<size_t,Result>> above;
  Stack<pair<size_t,Result>> below;

  bool sort = idx_x < idx_y;
  size_t idx_1 = sort ? idx_x : idx_y;
  size_t idx_2 = sort ? idx_y : idx_x;

  // z<x z<y
  for (size_t z_idx = 0; z_idx < idx_1; z_idx++) {
    Result r = Result(idx_of(z_idx, idx_x));
    if (/* r != none && */r != Result::INCOMPARABLE) {  // TODO wouldn't INC be propagated too?
      set_idx_of(z_idx, idx_y, resultToPoComp(r, false));
      above.push(make_pair(z_idx,r));
    } else {
      Result r = Result(idx_of(z_idx, idx_y));
      if (/* r != none && */r != Result::INCOMPARABLE) {
        set_idx_of(z_idx, idx_x, resultToPoComp(r, false));
        below.push(make_pair(z_idx,r));
      }
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      Result r = Result(idx_of(idx_x, z_idx));
      if (/* r != none && */r != Result::INCOMPARABLE) {
        set_idx_of(z_idx, idx_y, resultToPoComp(Ordering::reverse(r), true));
        above.push(make_pair(z_idx,Ordering::reverse(r)));
      } else {
        Result r = Result(idx_of(z_idx, idx_y));
        if (/* r != none && */r != Result::INCOMPARABLE) {
          set_idx_of(idx_x, z_idx, resultToPoComp(Ordering::reverse(r), true));
          below.push(make_pair(z_idx,r));
        }
      }
    }
  } else {
    // y<z<x
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      Result r = Result(idx_of(z_idx, idx_x));
      if (/* r != none && */r != Result::INCOMPARABLE) {
        set_idx_of(idx_y, z_idx, resultToPoComp(Ordering::reverse(r), true));
        above.push(make_pair(z_idx,r));
      } else {
        Result r = Result(idx_of(idx_y, z_idx));
        if (/* r != none && */r != Result::INCOMPARABLE) {
          set_idx_of(z_idx, idx_x, resultToPoComp(Ordering::reverse(r), true));
          below.push(make_pair(z_idx,Ordering::reverse(r)));
        }
      }
    }
  }

  // x<z y<z
  for (size_t z_idx = idx_2 + 1; z_idx < _size; z_idx++) {
    Result r = Result(idx_of(idx_x, z_idx));
    if (/* r != none && */r != Result::INCOMPARABLE) {
      set_idx_of(idx_y, z_idx, resultToPoComp(r, false));
      above.push(make_pair(z_idx,Ordering::reverse(r)));
    } else {
      Result r = Result(idx_of(idx_y, z_idx));
      if (/* r != none && */r != Result::INCOMPARABLE) {
        set_idx_of(idx_x, z_idx, resultToPoComp(r, false));
        below.push(make_pair(z_idx,Ordering::reverse(r)));
      }
    }
  }

  // cout << "after loop eq " << to_string() << endl;

  if (below.isNonEmpty()) {
    for (const auto& kv : above) {
      size_t x = kv.first;
      Result rx = kv.second;

      switch (rx) {
        case Result::EQUAL: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            Result ry = kv2.second;
            set_idx_of_safe(y, x, ry);
          }
          break;
        }
        case Result::GREATER: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            Result ry = kv2.second;
            switch (ry) {
              case Result::GREATER:
                break;
              case Result::EQUAL:
              case Result::LESS:
                set_idx_of_safe(x,y,Result::GREATER);
                break;
              case Result::INCOMPARABLE:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case Result::LESS: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            Result ry = kv2.second;
            switch (ry) {
              case Result::LESS:
                break;
              case Result::EQUAL:
              case Result::GREATER:
                set_idx_of_safe(x,y,Result::LESS);
                break;
              case Result::INCOMPARABLE:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case Result::INCOMPARABLE:
          ASSERTION_VIOLATION;
      }
    }
  }
}

void PartialOrdering::set_inferred(size_t idx_x, size_t idx_y, Result result)
{
  switch (result) {
    /* x > y: then ∀z. y ≥ z, also x > z,
               and ∀z. z ≥ x, also z > y */
    case Result::GREATER:
      set_inferred_loop(idx_x, idx_y, Result::GREATER, Result::LESS);
      break;
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case Result::LESS:
      set_inferred_loop(idx_x, idx_y, Result::LESS, Result::GREATER);
      break;
    /* x = y: then ∀z. z = x, also z = y
               and ∀z. z = y, also z = x
               and ∀z. z > x, also z > y
               and ∀z. z > y, also z > x
               and ∀z. z < x, also z < y
               and ∀z. z < y, also z < x */
    case Result::EQUAL:
      set_inferred_loop_eq(idx_x, idx_y);
      break;
    /* if INC then nothing can be inferred */
    case Result::INCOMPARABLE:
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

// string PartialOrdering::to_string_raw() const
// {
//   stringstream str;
//   typename DHMap<TermList,size_t>::Iterator vit(_nodes);
//   while (vit.hasNext()) {
//     TermList t;
//     size_t v;
//     vit.next(t,v);
//     str << t << " " << v << ", ";
//   }
//   str << "; ";
//   size_t arrSize = ((_size - 1) * _size / 2);
//   // for (size_t i = 0; i < arrSize; i++) {
//   //   str << Ordering::resultToStringInfix(_array[i]) << " ";
//   // }
//   return str.str();
// }

}
