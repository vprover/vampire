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
 * @file VarOrder.cpp
 */

#include "Forwards.hpp"
#include "Debug/TimeProfiling.hpp"
// #include "Lib/Metaiterators.hpp"

#include "VarOrder.hpp"

namespace Kernel {

using namespace std;

bool VarOrder::add_eq(unsigned x, unsigned y)
{
  if (x==y) {
    return true;
  }
  if (x < y) {
    swap(x,y);
  }
  auto& curr = _edges.get(x,y);
  if (curr == EQ) {
    return true;
  } else if (curr != UNSET) {
    return false;
  }
  curr = EQ;
  infer_transitive();
  return true;
}

bool VarOrder::add_gt(unsigned x, unsigned y)
{
  if (x==y) {
    return false;
  }
  auto val = x < y ? LT : GT;
  if (x < y) {
    swap(x,y);
  }
  auto& curr = _edges.get(x,y);
  if (curr == val) {
    return true;
  } else if (curr != UNSET) {
    return false;
  }
  curr = val;
  infer_transitive();
  return true;
}

inline VarOrder::Comp reverse(VarOrder::Comp c)
{
  switch(c) {
    case VarOrder::EQ:
    case VarOrder::UNSET:
      return c;
    case VarOrder::GT:
      return VarOrder::LT;
    case VarOrder::LT:
      return VarOrder::GT;
  }
}

VarOrder::Comp VarOrder::val(unsigned x, unsigned y) const
{
  return x < y ? reverse(_edges.get(y,x)) : _edges.get(x,y);
}

void VarOrder::set_val(unsigned x, unsigned y, VarOrder::Comp val)
{
  auto v = x < y ? reverse(val) : val;
  
  if (x < y) {
    ASS(_edges.get(y,x) == UNSET || _edges.get(y,x) == v);
    _edges.set(y,x,v);
  } else {
    ASS(_edges.get(x,y) == UNSET || _edges.get(x,y) == v);
    _edges.set(x,y,v);
  }
}

void VarOrder::complete_edge(unsigned i, unsigned j, unsigned k)
{
  auto ij = val(i,j);
  auto jk = val(j,k);
  // cout << i << " " << j << " " << k << " " << ij << " " << jk << endl;
  if (ij == VarOrder::UNSET || jk == VarOrder::UNSET) {
    return;
  }

  if (ij == VarOrder::EQ) {
    set_val(i,k,jk);
  } else if (ij == VarOrder::GT && jk != VarOrder::LT) {
    // c >= b > a
    set_val(i,k,VarOrder::GT);
  } else if (ij == VarOrder::LT && jk != VarOrder::GT) {
    // c <= b < a
    set_val(i,k,VarOrder::LT);
  }
}

void VarOrder::infer_transitive()
{
  for (unsigned i = 0; i < _vars; i++) {
    for (unsigned j = i+1; j < _vars; j++) {
      for (unsigned k = j+1; k < _vars; k++) {
        complete_edge(i,j,k);
        complete_edge(i,k,j);
        complete_edge(j,i,k);
      }
    }
  }
}

VarOrder VarOrder::transitive_reduction(const VarOrder& vo)
{
  VarOrder res(vo);
  for (unsigned i = 0; i < res._vars; i++) {
    res._edges.set(i,i,UNSET);
    for (unsigned j = i+1; j < res._vars; j++) {
      if (res._edges.get(j,i) == UNSET) {
        continue;
      }
      for (unsigned k = j+1; k < res._vars; k++) {
        if (res._edges.get(k,j) == UNSET) {
          continue;
        }
        // both ji and kj are set, remove third edge
        res._edges.set(k,i,UNSET);
      }
    }
  }
  return res;
}

VarOrders VarOrder::order_diff(const VarOrders& vos, const VarOrders& others)
{
  TIME_TRACE("order_diff");
  // cout << "vos " << vos << endl;
  // cout << "others " << others << endl;
  VarOrders res = vos;
  for (const auto& o : others) {
    auto tr = transitive_reduction(o);
    VarOrders new_res;
    for (const auto& vo : res) {
      for (unsigned i = 0; i < o._vars; i++) {
        for (unsigned j = i+1; j < o._vars; j++) {
          auto o_val = o._edges.get(j,i);
          auto vo_val = vo._edges.get(j,i);
          if (o_val == UNSET || o_val == vo_val) {
            continue;
          }
          if (vo_val != UNSET) {
            new_res.push(vo);
            continue;
            // break;
          }
          VarOrder one = vo;
          VarOrder two = vo;
          bool ov = true;
          bool tv = true;
          switch (o_val) {
            case EQ:
              ov=one.add_gt(j,i);
              tv=two.add_gt(i,j);
              break;
            case GT:
              ov=one.add_eq(j,i);
              tv=two.add_gt(i,j);
              break;
            case LT:
              ov=one.add_gt(j,i);
              tv=two.add_eq(j,i);
              break;
          }
          if (ov) {
            new_res.push(one);
          }
          if (tv) {
            new_res.push(two);
          }
          // break;
        }
      }
    }
    res = new_res;
  }
  // cout << "res " << res << endl << endl;
  return res;
}

// void VarOrder::order_diff(const VarOrder& vo, const VarOrders& others, VarOrders& res)
// {
//   VarOrders partial;
//   partial.push(vo);
//   TIME_TRACE("order_diff");
//   // if (others.isEmpty()) {
//   //   res.push(vo);
//   //   return;
//   // }
//   cout << "vo " << vo << endl;
//   cout << "others " << others << endl;
//   for (const auto& o : others) {
//     auto tr = transitive_reduction(o);
//     for (unsigned i = 0; i < o._vars; i++) {
//       for (unsigned j = i+1; j < o._vars; j++) {
//         auto o_val = o._edges.get(j,i);
//         auto vo_val = vo._edges.get(j,i);
//         if (o_val == UNSET || o_val == vo_val) {
//           continue;
//         }
//         if (vo_val != UNSET) {
//           if (!contains(res,vo)) {
//             res.push(vo);
//           }
//           continue;
//           // break; ?
//         }
//         VarOrder one = vo;
//         VarOrder two = vo;
//         bool ov = true;
//         bool tv = true;
//         switch (o_val) {
//           case EQ:
//             ov=one.add_gt(j,i);
//             tv=two.add_gt(i,j);
//             break;
//           case GT:
//             ov=one.add_eq(j,i);
//             tv=two.add_gt(i,j);
//             break;
//           case LT:
//             ov=one.add_gt(j,i);
//             tv=two.add_eq(j,i);
//             break;
//         }
//         if (ov && !contains(res,one)) {
//           res.push(one);
//         }
//         if (tv && !contains(res,two)) {
//           res.push(two);
//         }
//         // break; ?
//       }
//     }
//   }
//   cout << "res " << res << endl << endl;
// }

bool VarOrder::makeEqual(TermList tl1, TermList tl2, VarOrder& vo)
{
  if (tl1.isVar() && tl2.isVar()) {
    return vo.add_eq(tl1.var(),tl2.var());
  }
  if (!TermList::sameTopFunctor(tl1,tl2)) {
    return false;
  }

  Term* t1 = tl1.term();
  Term* t2 = tl2.term();
  ASS_EQ(t1->functor(),t2->functor());

  Stack<std::pair<TermList*,TermList*>> todo;
  todo.push(std::make_pair(t1->args(),t2->args()));
  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    auto ss = kv.first;
    auto tt = kv.second;
    if (ss->isEmpty()) {
      ASS(tt->isEmpty());
      continue;
    }
    todo.push(std::make_pair(ss->next(),tt->next()));

    if (ss->sameContent(tt)) {
      continue;
    }

    if (ss->isVar() && tt->isVar()) {
      if (!vo.add_eq(ss->var(),tt->var())) {
        return false;
      }
      continue;
    }

    if (!TermList::sameTopFunctor(*ss,*tt)) {
      return false;
    }

    todo.push(std::make_pair(ss->term()->args(),tt->term()->args()));
  }
  // std::cout << "makes equal " << tl1 << " and " << tl2 << " " << vo << std::endl;
  return true;
}

std::ostream& operator<<(std::ostream& out, const VarOrder& vo)
{
  bool set = false;
  out << "{ ";
  for (unsigned i = 0; i < vo._vars; i++) {
    for (unsigned j = i+1; j < vo._vars; j++) {
      auto val = vo._edges.get(j,i);
      if (val == VarOrder::UNSET) {
        continue;
      }
      if (set) {
        out << ", ";
      } else {
        set = true;
      }
      switch (val) {
        case VarOrder::EQ:
          out << "X" << j << " == X" << i;
          break;
        case VarOrder::GT:
          out << "X" << j << " > X" << i;
          break;
        case VarOrder::LT:
          out << "X" << j << " < X" << i;
          break;
      }
    }
  }
  out << " }";
  return out;
}

bool operator==(const VarOrder& vo1, const VarOrder& vo2)
{
  for (unsigned i = 0; i < vo1._vars; i++) {
    for (unsigned j = i+1; j < vo2._vars; j++) {
      if (vo1._edges.get(j,i) != vo2._edges.get(j,i)) {
        return false;
      }
    }
  }
  return true;
}

bool contains(const VarOrders& vos, const VarOrder& vo)
{
  for (const auto& other : vos) {
    if (other == vo) {
      return true;
    }
  }
  return false;
}

}