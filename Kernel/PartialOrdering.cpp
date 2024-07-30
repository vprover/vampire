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

#include "Debug/TimeProfiling.hpp"

namespace Kernel {

using namespace std;

template<typename T>
PartialOrdering<T>::PartialOrdering()
  : _nodes(), _inverse(), _size(0), _array(nullptr), _tr()
{
}

template<typename T>
PartialOrdering<T>::PartialOrdering(const PartialOrdering<T>& other)
  : _nodes(other._nodes), _inverse(other._inverse), _size(_nodes.size()), _array(nullptr), _tr()
{
  size_t arrSize = ((_size - 1) * _size / 2);
  if (arrSize) {
    void* mem = ALLOC_KNOWN(arrSize*sizeof(PoComp), "Kernel::PartialOrdering");
    _array = array_new<PoComp>(mem, arrSize);
    // std::memset(_array, PoComp::INCOMPARABLE, arrSize*sizeof(PoComp));
    memcpy(_array,other._array,arrSize*sizeof(PoComp));
  }
  _tr = List<Edge>::copy(other._tr);
}

template<typename T>
PartialOrdering<T>& PartialOrdering<T>::operator=(const PartialOrdering<T>& other)
{
  auto prevSize = ((_size - 1) * _size / 2);
  if (prevSize) {
    array_delete(_array, prevSize);
    DEALLOC_KNOWN(_array, prevSize*sizeof(PoComp), "Kernel::PartialOrdering");
  }
  _nodes.reset();
  _nodes.loadFromMap(other._nodes);
  _inverse.reset();
  _inverse.loadFromMap(other._inverse);
  _size = other._size;
  size_t arrSize = ((_size - 1) * _size / 2);
  if (arrSize) {
    void* mem = ALLOC_KNOWN(arrSize*sizeof(PoComp), "Kernel::PartialOrdering");
    _array = array_new<PoComp>(mem, arrSize);
    // std::memset(_array, PoComp::INCOMPARABLE, arrSize*sizeof(PoComp));
    memcpy(_array,other._array,arrSize*sizeof(PoComp));
  }
  _tr = List<Edge>::copy(other._tr);
  return *this;
}

template<typename T>
PartialOrdering<T>::~PartialOrdering()
{
  size_t arrSize = ((_size - 1) * _size / 2);
  if (arrSize) {
    array_delete(_array, arrSize);
    DEALLOC_KNOWN(_array, arrSize*sizeof(PoComp), "Kernel::PartialOrdering");
  }
  List<Edge>::destroy(_tr);
}

template<typename T>
bool PartialOrdering<T>::is_total() const
{
  size_t arrSize = ((_size - 1) * _size / 2);
  for (size_t i = 0; i < arrSize; i++) {
    if (_array[i]==PoComp::INCOMPARABLE) {
      return false;
    }
  }
  return true;
}

template<typename T>
PoComp PartialOrdering<T>::get(const T& x, const T& y) const
{
  if (x == y) {
    return PoComp::EQUAL;
  }
  if (!_nodes.find(x) || !_nodes.find(y)) {
    return PoComp::INCOMPARABLE;
  }
  size_t idx_x = idx_of_elem(x);
  size_t idx_y = idx_of_elem(y);
  if (idx_x < idx_y) {
    return idx_of(idx_x,idx_y);
  } else if (idx_y < idx_x) {
    return Ordering::reverse(idx_of(idx_y,idx_x));
  }
  return PoComp::EQUAL;
}

template<typename T>
bool PartialOrdering<T>::set(const T& x, const T& y, PoComp v)
{
  ASS_EQ(_size,_nodes.size());
  ASS(v != PoComp::INCOMPARABLE);
  size_t idx_x = idx_of_elem_ext(x);
  size_t idx_y = idx_of_elem_ext(y);
  // cout << "setting " << x << "->" << idx_x << " " << y << "->" << idx_y << " to " << Ordering::resultToStringInfix(v) << endl;
  if (idx_x == idx_y) {
    return v==PoComp::EQUAL;
  }
  PoComp curr = PoComp::INCOMPARABLE;
  if (idx_x < idx_y) {
    curr = idx_of(idx_x,idx_y);
  } else {
    curr = Ordering::reverse(idx_of(idx_y,idx_x));
  }
  // cout << "curr " << Ordering::resultToStringInfix(curr) << endl;
  if (curr != PoComp::INCOMPARABLE && curr != v) {
    return false;
  }
  set_idx_of_safe(idx_x,idx_y,v);
  // if (idx_x < idx_y) {
  //   set_idx_of(idx_x,idx_y,v);
  // } else {
  //   set_idx_of(idx_y,idx_x,Ordering::reverse(v));
  // }
  if (curr == PoComp::INCOMPARABLE) {
    set_inferred(idx_x,idx_y,v);
    // add to transitive reduction
    Edge e;
    if (v == PoComp::EQUAL || v == PoComp::GREATER) {
      e.x = x;
      e.y = y;
      e.c = v;
    } else {
      ASS(v != PoComp::INCOMPARABLE);
      e.x = y;
      e.y = x;
      e.c = Ordering::reverse(v);
    }
    List<Edge>::push(e, _tr);
  }
  // cout << "result " << to_string() << endl;
  return true;
}

template<typename T>
const T& PartialOrdering<T>::get_rep(const T& e) const
{
  const size_t* ptr = _nodes.findPtr(e);
  if (!ptr) {
    return e;
  }
  size_t idx_e = *ptr;
  for (size_t idx_o = 0; idx_o < idx_e; idx_o++) {
    if (idx_of(idx_o,idx_e) == PoComp::EQUAL) {
      return _inverse.get(idx_o);
    }
  }
  return e;
}

template<typename T>
size_t PartialOrdering<T>::idx_of_elem(const T& e) const
{
  ASS(_nodes.find(e));
  return _nodes.get(e);
}

template<typename T>
size_t PartialOrdering<T>::idx_of_elem_ext(const T& e)
{
  size_t *ptr;
  // cout << "size " << _size << endl;
  if (_nodes.getValuePtr(e, ptr, _size)) {
    ALWAYS(_inverse.insert(_size, e));
    // cout << "extend" << endl;
    // extend array
    size_t prevSize = ((_size - 1) * _size / 2);
    auto prevArray = _array;
    _size++;
    if (_size>1) {
      size_t newSize = prevSize + _size;
      void* mem = ALLOC_KNOWN(newSize*sizeof(PoComp), "Kernel::PartialOrdering");
      _array = array_new<PoComp>(mem, newSize);
      std::memset(_array, 0, newSize*sizeof(PoComp));
      for (unsigned i = prevSize; i < newSize; i++) {
        _array[i]=PoComp::INCOMPARABLE;
      }
      if (prevArray) {
        memcpy(_array,prevArray,prevSize*sizeof(T));
      }
      for (unsigned i = prevSize; i < newSize; i++) {
        ASS(_array[i]==PoComp::INCOMPARABLE);
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

template<typename T>
void PartialOrdering<T>::set_idx_of(size_t idx_x, size_t idx_y, PoComp v)
{
  size_t idx = idx_y*(idx_y-1)/2 + idx_x;
  ASS_L(idx,((_size - 1) * _size / 2));
  _array[idx] = v;
}

template<typename T>
void PartialOrdering<T>::set_idx_of_safe(size_t idx_x, size_t idx_y, PoComp v)
{
  if (idx_x < idx_y) {
    set_idx_of(idx_x,idx_y,v);
  } else {
    set_idx_of(idx_y,idx_x,Ordering::reverse(v));
  }
}

template<typename T>
PoComp PartialOrdering<T>::idx_of(size_t idx_x, size_t idx_y) const
{
  size_t idx = idx_y*(idx_y-1)/2 + idx_x;
  ASS_L(idx,((_size - 1) * _size / 2));
  return _array[idx];
}

template<typename T>
void PartialOrdering<T>::set_inferred_loop(size_t idx_x, size_t idx_y, PoComp gt, PoComp lt)
{
  ASS_NEQ(idx_x,idx_y);

  Stack<size_t> above;
  Stack<size_t> below;
  bool sort = idx_x < idx_y;
  size_t idx_1 = sort ? idx_x : idx_y;
  size_t idx_2 = sort ? idx_y : idx_x;

  // z<x z<y
  for (size_t z_idx = 0; z_idx < idx_1; z_idx++) {
    PoComp r = idx_of(z_idx, idx_x);
    if (r == gt || r == PoComp::EQUAL) {
      set_idx_of(z_idx, idx_y, gt);
      above.push(z_idx);
    } else {
      PoComp r = idx_of(z_idx, idx_y);
      if (r == lt || r == PoComp::EQUAL) {
        set_idx_of(z_idx, idx_x, lt);
        below.push(z_idx);
      }
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(idx_x, z_idx);
      if (r == lt || r == PoComp::EQUAL) {
        set_idx_of(z_idx, idx_y, gt);
        above.push(z_idx);
      } else {
        PoComp r = idx_of(z_idx, idx_y);
        if (r == lt || r == PoComp::EQUAL) {
          set_idx_of(idx_x, z_idx, gt);
          below.push(z_idx);
        }
      }
    }
  } else {
    // y<z<x
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(z_idx, idx_x);
      if (r == gt || r == PoComp::EQUAL) {
        set_idx_of(idx_y, z_idx, lt);
        above.push(z_idx);
      } else {
        PoComp r = idx_of(idx_y, z_idx);
        if (r == gt || r == PoComp::EQUAL) {
          set_idx_of(z_idx, idx_x, lt);
          below.push(z_idx);
        }
      }
    }
  }

  // x<z y<z
  for (size_t z_idx = idx_2 + 1; z_idx < _size; z_idx++) {
    PoComp r = idx_of(idx_x, z_idx);
    if (r == lt || r == PoComp::EQUAL) {
      set_idx_of(idx_y, z_idx, lt);
      above.push(z_idx);
    } else {
      PoComp r = idx_of(idx_y, z_idx);
      if (r == gt || r == PoComp::EQUAL) {
        set_idx_of(idx_x, z_idx, gt);
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

template<typename T>
void PartialOrdering<T>::set_inferred_loop_eq(size_t idx_x, size_t idx_y)
{
  ASS_NEQ(idx_x,idx_y);

  Stack<pair<size_t,PoComp>> above;
  Stack<pair<size_t,PoComp>> below;

  bool sort = idx_x < idx_y;
  size_t idx_1 = sort ? idx_x : idx_y;
  size_t idx_2 = sort ? idx_y : idx_x;

  // z<x z<y
  for (size_t z_idx = 0; z_idx < idx_1; z_idx++) {
    PoComp r = idx_of(z_idx, idx_x);
    if (/* r != none && */r != PoComp::INCOMPARABLE) {  // TODO wouldn't INC be propagated too?
      set_idx_of(z_idx, idx_y, r);
      above.push(make_pair(z_idx,r));
    } else {
      PoComp r = idx_of(z_idx, idx_y);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(z_idx, idx_x, r);
        below.push(make_pair(z_idx,r));
      }
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(idx_x, z_idx);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(z_idx, idx_y, Ordering::reverse(r));
        above.push(make_pair(z_idx,Ordering::reverse(r)));
      } else {
        PoComp r = idx_of(z_idx, idx_y);
        if (/* r != none && */r != PoComp::INCOMPARABLE) {
          set_idx_of(idx_x, z_idx, Ordering::reverse(r));
          below.push(make_pair(z_idx,r));
        }
      }
    }
  } else {
    // y<z<x
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(z_idx, idx_x);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(idx_y, z_idx, Ordering::reverse(r));
        above.push(make_pair(z_idx,r));
      } else {
        PoComp r = idx_of(idx_y, z_idx);
        if (/* r != none && */r != PoComp::INCOMPARABLE) {
          set_idx_of(z_idx, idx_x, Ordering::reverse(r));
          below.push(make_pair(z_idx,Ordering::reverse(r)));
        }
      }
    }
  }

  // x<z y<z
  for (size_t z_idx = idx_2 + 1; z_idx < _size; z_idx++) {
    PoComp r = idx_of(idx_x, z_idx);
    if (/* r != none && */r != PoComp::INCOMPARABLE) {
      set_idx_of(idx_y, z_idx, r);
      above.push(make_pair(z_idx,Ordering::reverse(r)));
    } else {
      PoComp r = idx_of(idx_y, z_idx);
      if (/* r != none && */r != PoComp::INCOMPARABLE) {
        set_idx_of(idx_x, z_idx, r);
        below.push(make_pair(z_idx,Ordering::reverse(r)));
      }
    }
  }

  // cout << "after loop eq " << to_string() << endl;

  if (below.isNonEmpty()) {
    for (const auto& kv : above) {
      size_t x = kv.first;
      PoComp rx = kv.second;

      switch (rx) {
        case PoComp::EQUAL: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            PoComp ry = kv2.second;
            set_idx_of_safe(y, x, ry);
          }
          break;
        }
        case PoComp::GREATER: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            PoComp ry = kv2.second;
            switch (ry) {
              case PoComp::GREATER:
                break;
              case PoComp::EQUAL:
              case PoComp::LESS:
                set_idx_of_safe(x,y,PoComp::GREATER);
                break;
              case PoComp::INCOMPARABLE:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case PoComp::LESS: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            PoComp ry = kv2.second;
            switch (ry) {
              case PoComp::LESS:
                break;
              case PoComp::EQUAL:
              case PoComp::GREATER:
                set_idx_of_safe(x,y,PoComp::LESS);
                break;
              case PoComp::INCOMPARABLE:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case PoComp::INCOMPARABLE:
          ASSERTION_VIOLATION;
      }
    }
  }
}

template<typename T>
void PartialOrdering<T>::set_inferred(size_t idx_x, size_t idx_y, PoComp result)
{
  switch (result) {
    /* x > y: then ∀z. y ≥ z, also x > z,
               and ∀z. z ≥ x, also z > y */
    case PoComp::GREATER:
      set_inferred_loop(idx_x, idx_y, PoComp::GREATER, PoComp::LESS);
      break;
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case PoComp::LESS:
      set_inferred_loop(idx_x, idx_y, PoComp::LESS, PoComp::GREATER);
      break;
    /* x = y: then ∀z. z = x, also z = y
               and ∀z. z = y, also z = x
               and ∀z. z > x, also z > y
               and ∀z. z > y, also z > x
               and ∀z. z < x, also z < y
               and ∀z. z < y, also z < x */
    case PoComp::EQUAL:
      set_inferred_loop_eq(idx_x, idx_y);
      break;
    /* if INC then nothing can be inferred */
    case PoComp::INCOMPARABLE:
      break;
  }
}

template<typename T>
string PartialOrdering<T>::to_string() const
{
  if (_nodes.size()<2) {
    return "{}";
  }
  stringstream str;
  typename DHMap<T,size_t>::Iterator vit1(_nodes);
  while (vit1.hasNext()) {
    T t1;
    size_t v1;
    vit1.next(t1,v1);
    typename DHMap<T,size_t>::Iterator vit2(_nodes);
    while (vit2.hasNext()) {
      T t2;
      size_t v2;
      vit2.next(t2,v2);
      if (v1 < v2) {
        auto c = idx_of(v1,v2);
        if (c == PoComp::INCOMPARABLE) {
          continue;
        }
        str << t1 << " " << Ordering::resultToStringInfix(c) << " " << t2 << " ";
      }
    }
  }
  return str.str();
}

template<typename T>
string PartialOrdering<T>::to_string_raw() const
{
  stringstream str;
  typename DHMap<T,size_t>::Iterator vit(_nodes);
  while (vit.hasNext()) {
    T t;
    size_t v;
    vit.next(t,v);
    str << t << " " << v << ", ";
  }
  str << "; ";
  size_t arrSize = ((_size - 1) * _size / 2);
  for (size_t i = 0; i < arrSize; i++) {
    str << Ordering::resultToStringInfix(_array[i]) << " ";
  }
  return str.str();
}

template<typename T>
VirtualIterator<std::tuple<T,T,PoComp>> PartialOrdering<T>::iter_relations() const
{
  ASSERTION_VIOLATION;
  // auto res = VirtualIterator<std::tuple<T,T,PoComp>>::getEmpty();
  // for (size_t idx_x = 0; idx_x < _size; idx_x++) {
  //   for (size_t idx_y = idx_x+1; idx_y < _size; idx_y++) {
  //     auto v = idx_of(idx_x,idx_y);
  //     if (v == PoComp::INCOMPARABLE) {
  //       continue;
  //     }
  //     res = pvi(getConcatenatedIterator(res,pvi(getSingletonIterator(make_tuple(_inverse.get(idx_x),_inverse.get(idx_y),v)))));
  //   }
  // }
  // return res;
}

template<typename T>
bool PartialOrdering<T>::subseteq(const PartialOrdering<T>& other) const
{
  for (size_t idx_x = 0; idx_x < _size; idx_x++) {
    for (size_t idx_y = idx_x+1; idx_y < _size; idx_y++) {
      auto v = idx_of(idx_x,idx_y);
      if (v == PoComp::INCOMPARABLE) {
        continue;
      }
      auto x = _inverse.get(idx_x);
      auto y = _inverse.get(idx_y);
      auto ptr_x = other._nodes.findPtr(x);
      if (!ptr_x) {
        return false;
      }
      auto ptr_y = other._nodes.findPtr(y);
      if (!ptr_y) {
        return false;
      }
      PoComp v_o;
      if (*ptr_x < *ptr_y) {
        v_o = other.idx_of(*ptr_x,*ptr_y);
      } else {
        v_o = Ordering::reverse(other.idx_of(*ptr_y,*ptr_x));
      }
      if (v != v_o) {
        return false;
      }
    }
  }
  return true;
}

template class PartialOrdering<unsigned>;

}