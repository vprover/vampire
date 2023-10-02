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
 * @file EqHelper.cpp
 * Implements class EqHelper.
 */

#include "PartialOrdering.hpp"
#include "Lib/Stack.hpp"

namespace Kernel {

using namespace std;

vstring toString(PoComp comp)
{
  switch (comp) {
    case PoComp::EQ:
      return "=";
    case PoComp::INC:
      return "?";
    case PoComp::GT:
      return ">";
    case PoComp::LT:
      return "<";
  }
}

PoComp reverse(PoComp comp)
{
  switch (comp) {
    case PoComp::EQ:
    case PoComp::INC:
      return comp;
    case PoComp::GT:
      return PoComp::LT;
    case PoComp::LT:
      return PoComp::GT;
  }
}

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
    // std::memset(_array, 0, arrSize*sizeof(PoComp));
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
    // std::memset(_array, 0, arrSize*sizeof(PoComp));
    memcpy(_array,other._array,arrSize*sizeof(PoComp));
  }
  _tr = List<Edge>::copy(other._tr);
  return *this;
}

// let copy g = 
//   {g with table = Array.copy g.table}

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
    if (_array[i]==PoComp::INC) {
      return false;
    }
  }
  return true;
}

template<typename T>
PoComp PartialOrdering<T>::get(const T& x, const T& y) const
{
  if (x == y) {
    return PoComp::EQ;
  }
  if (!_nodes.find(x) || !_nodes.find(y)) {
    return PoComp::INC;
  }
  size_t idx_x = idx_of_elem(x);
  size_t idx_y = idx_of_elem(y);
  if (idx_x < idx_y) {
    return idx_of(idx_x,idx_y);
  } else if (idx_y < idx_x) {
    return reverse(idx_of(idx_y,idx_x));
  }
  return PoComp::EQ;
}

template<typename T>
bool PartialOrdering<T>::set(const T& x, const T& y, PoComp v)
{
  ASS_EQ(_size,_nodes.size());
  ASS(v != PoComp::INC);
  size_t idx_x = idx_of_elem_ext(x);
  size_t idx_y = idx_of_elem_ext(y);
  // cout << "setting " << x << "->" << idx_x << " " << y << "->" << idx_y << " to " << toString(v) << endl;
  if (idx_x == idx_y) {
    return v==PoComp::EQ;
  }
  PoComp curr = PoComp::INC;
  if (idx_x < idx_y) {
    curr = idx_of(idx_x,idx_y);
  } else {
    curr = reverse(idx_of(idx_y,idx_x));
  }
  // cout << "curr " << toString(curr) << endl;
  if (curr != PoComp::INC && curr != v) {
    return false;
  }
  set_idx_of_safe(idx_x,idx_y,v);
  // if (idx_x < idx_y) {
  //   set_idx_of(idx_x,idx_y,v);
  // } else {
  //   set_idx_of(idx_y,idx_x,reverse(v));
  // }
  if (curr == PoComp::INC) {
    set_inferred(idx_x,idx_y,v);
    // add to transitive reduction
    Edge e;
    if (v == PoComp::EQ || v == PoComp::GT) {
      e.x = x;
      e.y = y;
      e.c = v;
    } else {
      ASS(v != PoComp::INC);
      e.x = y;
      e.y = x;
      e.c = reverse(v);
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
    if (idx_of(idx_o,idx_e) == PoComp::EQ) {
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
      if (prevArray) {
        memcpy(_array,prevArray,prevSize*sizeof(T));
      }
      for (unsigned i = prevSize; i < newSize; i++) {
        ASS(_array[i]==PoComp::INC);
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
    set_idx_of(idx_y,idx_x,reverse(v));
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
    if (r == gt || r == PoComp::EQ) {
      set_idx_of(z_idx, idx_y, gt);
      above.push(z_idx);
    } else {
      PoComp r = idx_of(z_idx, idx_y);
      if (r == lt || r == PoComp::EQ) {
        set_idx_of(z_idx, idx_x, lt);
        below.push(z_idx);
      }
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(idx_x, z_idx);
      if (r == lt || r == PoComp::EQ) {
        set_idx_of(z_idx, idx_y, gt);
        above.push(z_idx);
      } else {
        PoComp r = idx_of(z_idx, idx_y);
        if (r == lt || r == PoComp::EQ) {
          set_idx_of(idx_x, z_idx, gt);
          below.push(z_idx);
        }
      }
    }
  } else {
    // y<z<x
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(z_idx, idx_x);
      if (r == gt || r == PoComp::EQ) {
        set_idx_of(idx_y, z_idx, lt);
        above.push(z_idx);
      } else {
        PoComp r = idx_of(idx_y, z_idx);
        if (r == gt || r == PoComp::EQ) {
          set_idx_of(z_idx, idx_x, lt);
          below.push(z_idx);
        }
      }
    }
  }

  // x<z y<z
  for (size_t z_idx = idx_2 + 1; z_idx < _size; z_idx++) {
    PoComp r = idx_of(idx_x, z_idx);
    if (r == lt || r == PoComp::EQ) {
      set_idx_of(idx_y, z_idx, lt);
      above.push(z_idx);
    } else {
      PoComp r = idx_of(idx_y, z_idx);
      if (r == gt || r == PoComp::EQ) {
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
    if (/* r != none && */r != PoComp::INC) {  // TODO wouldn't INC be propagated too?
      set_idx_of(z_idx, idx_y, r);
      above.push(make_pair(z_idx,r));
    } else {
      PoComp r = idx_of(z_idx, idx_y);
      if (/* r != none && */r != PoComp::INC) {
        set_idx_of(z_idx, idx_x, r);
        below.push(make_pair(z_idx,r));
      }
    }
  }

  if (sort) {
    // x<z<y
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(idx_x, z_idx);
      if (/* r != none && */r != PoComp::INC) {
        set_idx_of(z_idx, idx_y, reverse(r));
        above.push(make_pair(z_idx,reverse(r)));
      } else {
        PoComp r = idx_of(z_idx, idx_y);
        if (/* r != none && */r != PoComp::INC) {
          set_idx_of(idx_x, z_idx, reverse(r));
          below.push(make_pair(z_idx,r));
        }
      }
    }
  } else {
    // y<z<x
    for (size_t z_idx = idx_1 + 1; z_idx < idx_2; z_idx++) {
      PoComp r = idx_of(z_idx, idx_x);
      if (/* r != none && */r != PoComp::INC) {
        set_idx_of(idx_y, z_idx, reverse(r));
        above.push(make_pair(z_idx,r));
      } else {
        PoComp r = idx_of(idx_y, z_idx);
        if (/* r != none && */r != PoComp::INC) {
          set_idx_of(z_idx, idx_x, reverse(r));
          below.push(make_pair(z_idx,reverse(r)));
        }
      }
    }
  }

  // x<z y<z
  for (size_t z_idx = idx_2 + 1; z_idx < _size; z_idx++) {
    PoComp r = idx_of(idx_x, z_idx);
    if (/* r != none && */r != PoComp::INC) {
      set_idx_of(idx_y, z_idx, r);
      above.push(make_pair(z_idx,reverse(r)));
    } else {
      PoComp r = idx_of(idx_y, z_idx);
      if (/* r != none && */r != PoComp::INC) {
        set_idx_of(idx_x, z_idx, r);
        below.push(make_pair(z_idx,reverse(r)));
      }
    }
  }

  // cout << "after loop eq " << to_string() << endl;

  if (below.isNonEmpty()) {
    for (const auto& kv : above) {
      size_t x = kv.first;
      PoComp rx = kv.second;

      switch (rx) {
        case PoComp::EQ: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            PoComp ry = kv2.second;
            set_idx_of_safe(y, x, ry);
          }
          break;
        }
        case PoComp::GT: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            PoComp ry = kv2.second;
            switch (ry) {
              case PoComp::GT:
                break;
              case PoComp::EQ:
              case PoComp::LT:
                set_idx_of_safe(x,y,PoComp::GT);
                break;
              case PoComp::INC:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case PoComp::LT: {
          for (const auto& kv2 : below) {
            size_t y = kv2.first;
            PoComp ry = kv2.second;
            switch (ry) {
              case PoComp::LT:
                break;
              case PoComp::EQ:
              case PoComp::GT:
                set_idx_of_safe(x,y,PoComp::LT);
                break;
              case PoComp::INC:
                ASSERTION_VIOLATION;
            }
          }
          break;
        }
        case PoComp::INC:
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
    case PoComp::GT:
      set_inferred_loop(idx_x, idx_y, PoComp::GT, PoComp::LT);
      break;
    /* x < y: then ∀z. y ≤ z, also x < z,
               and ∀z. z ≤ x, also z < y */
    case PoComp::LT:
      set_inferred_loop(idx_x, idx_y, PoComp::LT, PoComp::GT);
      break;
    /* x = y: then ∀z. z = x, also z = y
               and ∀z. z = y, also z = x
               and ∀z. z > x, also z > y
               and ∀z. z > y, also z > x
               and ∀z. z < x, also z < y
               and ∀z. z < y, also z < x */
    case PoComp::EQ:
      set_inferred_loop_eq(idx_x, idx_y);
      break;
    /* if INC then nothing can be inferred */
    case PoComp::INC:
      break;
  }
}

template<typename T>
vstring PartialOrdering<T>::to_string() const
{
  vstringstream str;
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
        if (c == PoComp::INC) {
          continue;
        }
        str << t1 << " " << toString(c) << " " << t2 << " ";
      }
    }
  }
  return str.str();
}

template<typename T>
vstring PartialOrdering<T>::to_string_raw() const
{
  vstringstream str;
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
    str << toString(_array[i]) << " ";
  }
  return str.str();
}

template class PartialOrdering<unsigned>;


  // let set_unsafe g x y v = 
  //   let x_idx = idx_of_elem g x in
  //   let y_idx = idx_of_elem g y in
  //   set' g x_idx y_idx v

  // type res = Eq | Ne | Invalid
  // let set g x y v = 
  //   let x_idx = idx_of_elem'' g x in
  //   let y_idx = idx_of_elem'' g y in
  //   let old_v = get' g x_idx y_idx in
  //   if old_v == none then (
  //     set' g x_idx y_idx v;
  //     set_inferred' g x_idx y_idx v;
  //     Ne
  //   ) else if old_v == v then (
  //     Eq
  //   ) else (
  //     Invalid
  //   )

  // let mem g x = 
  //   (* let rec loop g x_idx z_idx max_idx = 
  //     if z_idx >= max_idx then
  //       false
  //     else
  //       g.table.(idx_of x)
  //   in
  //   let x_idx = idx_of_elem g x in
  //   loop g x_idx (0) (x_idx-1) || loop g x_idx (x_idx+1) (g.size-1) *)
  //   g.nodes |> M.mem x

  // let iter_elts g f = 
  //   g.nodes |> M.iter (fun x _ -> f x)

  // let iter_relations g f = 
  //   let rec loop g f l = 
  //     let rec loop' g f x l = 
  //       match l with
  //       | y::tl -> 
  //         let (x_elt, x_idx) = x in
  //         let (y_elt, y_idx) = y in
  //         let res = get' g x_idx y_idx in
  //         if res != none then f x_elt y_elt res;
  //         loop' g f x tl
  //       | [] -> ()
  //     in
  //     match l with
  //     | x::tl -> loop' g f x tl; loop g f tl
  //     | [] -> ()
  //   in
  //   loop g f (M.bindings g.nodes)



  // let update' g x_idx y_idx f = 
  //   if x_idx < y_idx then
  //     let idx_cmp = idx_of g x_idx y_idx in
  //     let x = g.table.(idx_cmp) in
  //     let y = f x in
  //     g.table.(idx_cmp) <- y
  //   else if x_idx > y_idx then
  //     let idx_cmp = idx_of g y_idx x_idx in
  //     let x = PartialOrd.reverse @@ g.table.(idx_cmp) in
  //     let y = f x in
  //     g.table.(idx_cmp) <- PartialOrd.reverse y
  //   else
  //     ()

  // (* Add a list of nodes which are linearly sorted *)
  // (* Invariant: graph is empty (current) *)
  // let add_sorted g l =
  //   dassert (fun () -> 
  //     g.table |> Array.for_all (fun x -> x == none)
  //   );
  //   let rec loop g l = 
  //     match l with
  //     | [_] -> ()
  //     | hd::(_::_ as tl) -> 
  //       tl |> List.iter (fun x -> 
  //         set' g hd x (if hd == x then EQ else LT)  (* Here was always LT, which is incorrect and results in slightly weaker normalisation in AC *)
  //       );
  //       loop g tl
  //     | [] -> (* assert false; *) ()
  //   in
  //   let l_idx = List.map (fun x -> idx_of_elem g x) l in
  //   loop g l_idx

  // let add_with g cmp x =
  //   (* From list of nodes, compare with every other node *)
  //   let x_idx = idx_of_elem g x in
  //   g.nodes |> M.iter (fun y y_idx ->
  //     update' g x_idx y_idx (fun res -> 
  //       if res != none then res else (
  //         let result = cmp x y in
  //         set_inferred' g x_idx y_idx result;
  //         result
  //       )
  //     )
  //   )

  // let add_with_many g cmp l = 
  //   List.iter (add_with g cmp) l



  // let wrap g f x y = 
  //   let x_idx = idx_of_elem g x in
  //   let y_idx = idx_of_elem g y in
  //   if x_idx < y_idx then
  //     let idx_cmp = idx_of g x_idx y_idx in
  //     let r = g.table.(idx_cmp) in
  //     if r != none then r else (
  //       let r' = f x y in
  //       g.table.(idx_cmp) <- r';
  //       set_inferred' g x_idx y_idx r';
  //       r'
  //     )
  //   else if x_idx > y_idx then
  //     let idx_cmp = idx_of g y_idx x_idx in
  //     let r = g.table.(idx_cmp) in
  //     if r != none then PartialOrd.reverse r else (
  //       let r' = f y x in
  //       g.table.(idx_cmp) <- r';
  //       set_inferred' g y_idx x_idx r';
  //       PartialOrd.reverse r'
  //     )
  //   else
  //     EQ



}
