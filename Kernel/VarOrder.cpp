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

bool VarOrder::add_gt(unsigned x, unsigned y)
{
  return _po.set(x, y, PoComp::GT);
}

bool VarOrder::add_eq(unsigned x, unsigned y)
{
  return _po.set(x, y, PoComp::EQ);
}

PoComp VarOrder::query(unsigned x, unsigned y) const
{
  return _po.get(x, y);
}

bool VarOrder::is_total(size_t n) const
{
  return _po.size() == n && _po.is_total();
}

vstring VarOrder::to_string() const
{
  // return Int::toString(_po.size()) + ": " + _po.to_string() + ", " + _po.to_string_raw();
  return _po.to_string();
}

const List<Edge>* VarOrder::transitive_reduction() const
{
  return _po.transitive_reduction();
}

bool VarOrder::is_empty() const
{
  return _po.size() < 2;
}

TermList VarOrder::EqApplicator::apply(unsigned v)
{
  return TermList(_vo._po.get_rep(v),false);
}

VirtualIterator<std::tuple<const unsigned&,const unsigned&,PoComp>> VarOrder::iter_relations() const
{
  return _po.iter_relations();
}

size_t VarOrder::rel_size() const
{
  return _po.size();
}

bool VarOrder::subseteq(const VarOrder& other) const
{
  return _po.subseteq(other._po);
}

// bool VarOrder::add_eq(unsigned x, unsigned y)
// {
//   ASS(hasVar(x));
//   ASS(hasVar(y));
//   // if (!hasVar(x) || !hasVar(y)) {
//   //   return false;
//   // }
//   if (x==y) {
//     return true;
//   }
//   auto x_val = _vars.get(x);
//   auto y_val = _vars.get(y);
//   if (x_val < y_val) {
//     swap(x_val,y_val);
//   }
//   auto& curr = _edges->get(x_val,y_val);
//   if (curr == EQ) {
//     return true;
//   } else if (curr != UNSET) {
//     return false;
//   }
//   curr = EQ;
//   infer_transitive();
//   return true;
// }

// bool VarOrder::add_gt(unsigned x, unsigned y)
// {
//   ASS(hasVar(x));
//   ASS(hasVar(y));
//   if (x==y) {
//     return false;
//   }
//   auto x_val = _vars.get(x);
//   auto y_val = _vars.get(y);
//   auto val = x_val < y_val ? LT : GT;
//   if (x_val < y_val) {
//     swap(x_val,y_val);
//   }
//   auto& curr = _edges->get(x_val,y_val);
//   if (curr == val) {
//     return true;
//   } else if (curr != UNSET) {
//     return false;
//   }
//   curr = val;
//   infer_transitive();
//   return true;
// }

// inline VarOrder::Comp reverse(VarOrder::Comp c)
// {
//   switch(c) {
//     case VarOrder::EQ:
//     case VarOrder::UNSET:
//       return c;
//     case VarOrder::GT:
//       return VarOrder::LT;
//     case VarOrder::LT:
//       return VarOrder::GT;
//   }
// }

// VarOrder::Comp VarOrder::val(unsigned x, unsigned y) const
// {
//   if (x == y) {
//     return VarOrder::Comp::EQ;
//   }
//   auto x_val = _vars.get(x);
//   auto y_val = _vars.get(y);
//   return x_val < y_val ? reverse(_edges->get(y_val,x_val)) : _edges->get(x_val,y_val);
// }

// void VarOrder::set_val(unsigned x, unsigned y, VarOrder::Comp val)
// {
//   ASS_NEQ(x,y);
//   auto x_val = _vars.get(x);
//   auto y_val = _vars.get(y);
//   auto v = x_val < y_val ? reverse(val) : val;
  
//   if (x_val < y_val) {
//     ASS(_edges->get(y_val,x_val) == UNSET || _edges->get(y_val,x_val) == v);
//     _edges->set(y_val,x_val,v);
//   } else {
//     ASS(_edges->get(x_val,y_val) == UNSET || _edges->get(x_val,y_val) == v);
//     _edges->set(x_val,y_val,v);
//   }
// }

// VarOrder::Comp VarOrder::get(unsigned x, unsigned y) const
// {
//   return _edges->get(x,y);
// }

// void VarOrder::set(unsigned x, unsigned y, VarOrder::Comp val)
// {
//   ASS_G(x,y);
//   _edges->set(x,y,val);
// }

// void VarOrder::complete_edge(unsigned i, unsigned j, unsigned k)
// {
//   auto ij = val(i,j);
//   auto jk = val(j,k);
//   // cout << i << " " << j << " " << k << " " << ij << " " << jk << endl;
//   if (ij == VarOrder::UNSET || jk == VarOrder::UNSET) {
//     return;
//   }

//   if (ij == VarOrder::EQ) {
//     set_val(i,k,jk);
//   } else if (ij == VarOrder::GT && jk != VarOrder::LT) {
//     // c >= b > a
//     set_val(i,k,VarOrder::GT);
//   } else if (ij == VarOrder::LT && jk != VarOrder::GT) {
//     // c <= b < a
//     set_val(i,k,VarOrder::LT);
//   }
// }

// void VarOrder::infer_transitive()
// {
//   for (unsigned i = 0; i < _vars.size(); i++) {
//     for (unsigned j = i+1; j < _vars.size(); j++) {
//       for (unsigned k = j+1; k < _vars.size(); k++) {
//         complete_edge(i,j,k);
//         complete_edge(i,k,j);
//         complete_edge(j,i,k);
//       }
//     }
//   }
// }

// VarOrder VarOrder::transitive_reduction(const VarOrder& vo)
// {
//   VarOrder res(vo);
//   for (unsigned i = 0; i < res._vars.size(); i++) {
//     res._edges->set(i,i,UNSET);
//     for (unsigned j = i+1; j < res._vars.size(); j++) {
//       if (res._edges->get(j,i) == UNSET) {
//         continue;
//       }
//       for (unsigned k = j+1; k < res._vars.size(); k++) {
//         if (res._edges->get(k,j) == UNSET) {
//           continue;
//         }
//         // both ji and kj are set, remove third edge
//         res._edges->set(k,i,UNSET);
//       }
//     }
//   }
//   return res;
// }

// VarOrders VarOrder::order_diff(const VarOrders& vos, const VarOrders& others)
// {
//   TIME_TRACE("order_diff");
//   // cout << "vos " << vos << endl;
//   // cout << "others " << others << endl;
//   VarOrders res = vos;
//   for (const auto& o : others) {
//     auto tr = transitive_reduction(o);
//     VarOrders new_res;
//     for (const auto& vo : res) {
//       for (unsigned i = 0; i < o._vars.size(); i++) {
//         for (unsigned j = i+1; j < o._vars.size(); j++) {
//           auto o_val = o._edges->get(j,i);
//           auto vo_val = vo._edges->get(j,i);
//           if (o_val == UNSET || o_val == vo_val) {
//             continue;
//           }
//           if (vo_val != UNSET) {
//             new_res.push(vo);
//             continue;
//             // break;
//           }
//           VarOrder one = vo;
//           VarOrder two = vo;
//           bool ov = true;
//           bool tv = true;
//           switch (o_val) {
//             case EQ:
//               ov=one.add_gt(j,i);
//               tv=two.add_gt(i,j);
//               break;
//             case GT:
//               ov=one.add_eq(j,i);
//               tv=two.add_gt(i,j);
//               break;
//             case LT:
//               ov=one.add_gt(j,i);
//               tv=two.add_eq(j,i);
//               break;
//           }
//           if (ov) {
//             new_res.push(one);
//           }
//           if (tv) {
//             new_res.push(two);
//           }
//           // break;
//         }
//       }
//     }
//     res = new_res;
//   }
//   // cout << "res " << res << endl << endl;
//   return res;
// }

// // void VarOrder::order_diff(const VarOrder& vo, const VarOrders& others, VarOrders& res)
// // {
// //   VarOrders partial;
// //   partial.push(vo);
// //   TIME_TRACE("order_diff");
// //   // if (others.isEmpty()) {
// //   //   res.push(vo);
// //   //   return;
// //   // }
// //   cout << "vo " << vo << endl;
// //   cout << "others " << others << endl;
// //   for (const auto& o : others) {
// //     auto tr = transitive_reduction(o);
// //     for (unsigned i = 0; i < o._vars; i++) {
// //       for (unsigned j = i+1; j < o._vars; j++) {
// //         auto o_val = o._edges.get(j,i);
// //         auto vo_val = vo._edges.get(j,i);
// //         if (o_val == UNSET || o_val == vo_val) {
// //           continue;
// //         }
// //         if (vo_val != UNSET) {
// //           if (!contains(res,vo)) {
// //             res.push(vo);
// //           }
// //           continue;
// //           // break; ?
// //         }
// //         VarOrder one = vo;
// //         VarOrder two = vo;
// //         bool ov = true;
// //         bool tv = true;
// //         switch (o_val) {
// //           case EQ:
// //             ov=one.add_gt(j,i);
// //             tv=two.add_gt(i,j);
// //             break;
// //           case GT:
// //             ov=one.add_eq(j,i);
// //             tv=two.add_gt(i,j);
// //             break;
// //           case LT:
// //             ov=one.add_gt(j,i);
// //             tv=two.add_eq(j,i);
// //             break;
// //         }
// //         if (ov && !contains(res,one)) {
// //           res.push(one);
// //         }
// //         if (tv && !contains(res,two)) {
// //           res.push(two);
// //         }
// //         // break; ?
// //       }
// //     }
// //   }
// //   cout << "res " << res << endl << endl;
// // }

// bool VarOrder::makeEqual(TermList tl1, TermList tl2, VarOrder& vo)
// {
//   if (tl1.isVar() && tl2.isVar()) {
//     return vo.add_eq(tl1.var(),tl2.var());
//   }
//   if (!TermList::sameTopFunctor(tl1,tl2)) {
//     return false;
//   }

//   Term* t1 = tl1.term();
//   Term* t2 = tl2.term();
//   ASS_EQ(t1->functor(),t2->functor());

//   Stack<std::pair<TermList*,TermList*>> todo;
//   todo.push(std::make_pair(t1->args(),t2->args()));
//   while (todo.isNonEmpty()) {
//     auto kv = todo.pop();
//     auto ss = kv.first;
//     auto tt = kv.second;
//     if (ss->isEmpty()) {
//       ASS(tt->isEmpty());
//       continue;
//     }
//     todo.push(std::make_pair(ss->next(),tt->next()));

//     if (ss->sameContent(tt)) {
//       continue;
//     }

//     if (ss->isVar() && tt->isVar()) {
//       if (!vo.add_eq(ss->var(),tt->var())) {
//         return false;
//       }
//       continue;
//     }

//     if (!TermList::sameTopFunctor(*ss,*tt)) {
//       return false;
//     }

//     todo.push(std::make_pair(ss->term()->args(),tt->term()->args()));
//   }
//   // std::cout << "makes equal " << tl1 << " and " << tl2 << " " << vo << std::endl;
//   return true;
// }

// std::ostream& operator<<(std::ostream& out, const VarOrder& vo)
// {
//   bool set = false;
//   out << "{ ";
//   auto outer = vo.iterVars();
//   while (outer.hasNext()) {
//     auto x = outer.next();
//     auto inner = vo.iterVars();
//     while (inner.hasNext()) {
//       auto y = inner.next();
//       if (x <= y) {
//         continue;
//       }
//       auto val = vo.val(x,y);
//       if (set) {
//         out << ", ";
//       } else {
//         set = true;
//       }
//       switch (val) {
//         case VarOrder::EQ:
//           out << "X" << x << " == X" << y;
//           break;
//         case VarOrder::GT:
//           out << "X" << x << " > X" << y;
//           break;
//         case VarOrder::LT:
//           out << "X" << x << " < X" << y;
//           break;
//       }
//     }
//   }
//   out << " }";
//   return out;
// }

// bool operator==(const VarOrder& vo1, const VarOrder& vo2)
// {
//   ASS_EQ(vo1.numVars(),vo2.numVars());
//   for (unsigned i = 0; i < vo1.numVars(); i++) {
//     for (unsigned j = i+1; j < vo2.numVars(); j++) {
//       if (vo1._edges->get(j,i) != vo2._edges->get(j,i)) {
//         return false;
//       }
//     }
//   }
//   return true;
// }

// bool contains(const VarOrders& vos, const VarOrder& vo)
// {
//   for (const auto& other : vos) {
//     if (other == vo) {
//       return true;
//     }
//   }
//   return false;
// }

// std::ostream& operator<<(std::ostream& out, const TriangularArray<VarOrder::Comp>& edges)
// {
//   bool set = false;
//   out << "{ ";
//   for (unsigned i = 0; i < edges.size(); i++) {
//     for (unsigned j = i+1; j < edges.size(); j++) {
//       auto val = edges.get(j,i);
//       if (val == VarOrder::UNSET) {
//         continue;
//       }
//       if (set) {
//         out << ", ";
//       } else {
//         set = true;
//       }
//       switch (val) {
//         case VarOrder::EQ:
//           out << "X" << j << " == X" << i;
//           break;
//         case VarOrder::GT:
//           out << "X" << j << " > X" << i;
//           break;
//         case VarOrder::LT:
//           out << "X" << j << " < X" << i;
//           break;
//       }
//     }
//   }
//   out << " }";
//   return out;
// }

// TermList VarOrderEqApplicator::apply(unsigned v)
// {
//   if (!_vo.hasVar(v)) {
//     return TermList(v,false);
//   }

//   auto vit = _vo.iterVars();
//   while (vit.hasNext()) {
//     auto i = vit.next();
//     if (i >= v) {
//       continue;
//     }
//     if (_vo.val(i,v)==VarOrder::EQ) {
//       return TermList(i,false);
//     }
//   }
//   return TermList(v,false);
// }

// bool findNextOrder(TriangularArray<VarOrder::Comp>& edges, unsigned size) {
//   TIME_TRACE("findNextOrder");
//   while (true) {
//     for (unsigned i = 0; i < size; i++) {
//       for (unsigned j = i+1; j < size; j++) {
//         auto v = static_cast<unsigned>(edges.get(j,i))+1;
//         if (v == 4) {
//           // overflow
//           edges.set(j,i,VarOrder::EQ);
//         } else {
//           ASS_L(v,4);
//           edges.set(j,i,static_cast<VarOrder::Comp>(v));
//           // cout << "possible " << edges << endl;
//           goto found;
//         }
//       }
//     }
//     return false; // everything overflowed, no more values

// found:
//     // check transitivity
//     TIME_TRACE("check transitivity");
//     for (unsigned i = 0; i < size; i++) {
//       for (unsigned j = i+1; j < size; j++) {
//         for (unsigned k = j+1; k < size; k++) {
//           auto ji = edges.get(j,i);
//           auto kj = edges.get(k,j);
//           auto ki = edges.get(k,i);
//           ASS_NEQ(ji,VarOrder::UNSET);
//           ASS_NEQ(kj,VarOrder::UNSET);
//           ASS_NEQ(ki,VarOrder::UNSET);
//           auto check_triangle = [](VarOrder::Comp ij, VarOrder::Comp jk, VarOrder::Comp ik) {
//             if (ij == VarOrder::EQ) {
//               return ik == jk;
//             } else if (ij == VarOrder::GT && jk != VarOrder::LT) {
//               // i > j >= k
//               return ik == VarOrder::GT;
//             } else if (ij == VarOrder::LT && jk != VarOrder::GT) {
//               // c <= b < a
//               return ik == VarOrder::LT;
//             }
//             return true;
//           };
//           if (!check_triangle(ji,reverse(ki),reverse(kj)) || !check_triangle(kj,ji,ki) || !check_triangle(reverse(ki),kj,reverse(ji))) {
//             // cout << "X" << i << " X" << j << " X" << k << " contradict" << endl;
//             goto next;
//           }
//         }
//       }
//     }
//     // cout << "end " << edges << endl;
//     return true;
// next:
//     continue;
//   }
//   return false;
// }

// bool VarOrder::getVarOrder(unsigned size, unsigned index, VarOrder& vo)
// {
//   if (size < 2) {
//     if (index>0) {
//       return false;
//     }
//     return true;
//   }
//   static DHMap<unsigned,Stack<TriangularArray<VarOrder::Comp>*>> _cache;
//   Stack<TriangularArray<VarOrder::Comp>*>* ptr = nullptr;
//   if (_cache.getValuePtr(size,ptr)) {
//     TriangularArray<Comp> edges(size);
//     // start with all EQ
//     for (unsigned i = 0; i < size; i++) {
//       for (unsigned j = i+1; j < size; j++) {
//         edges.set(j,i,VarOrder::EQ);
//       }
//     }
//     do {
//       auto curr = new TriangularArray<Comp>(size);
//       for (unsigned i = 0; i < size; i++) {
//         for (unsigned j = i+1; j < size; j++) {
//           curr->set(j,i,edges.get(j,i));
//         }
//       }
//       ptr->push(curr);
//     } while (findNextOrder(edges, size));
//   }
//   if (index < ptr->size()) {
//     vo.setEdges((*ptr)[index]);
//     return true;
//   }
//   return false;
// }

}