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

VirtualIterator<std::tuple<unsigned,unsigned,PoComp>> VarOrder::iter_relations() const
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

bool VarOrder::tryExtendWith(const VarOrder& other)
{
  auto tr = other.transitive_reduction();
  while (List<Edge>::isNonEmpty(tr)) {
    auto e = tr->head();
    if (e.c == PoComp::EQ) {
      if (!add_eq(e.x,e.y)) {
        return false;
      }
    } else if (e.c == PoComp::GT) {
      if (!add_gt(e.x,e.y)) {
        return false;
      }
    } else if (e.c == PoComp::LT) {
      if (!add_gt(e.y,e.x)) {
        return false;
      }
    }
    tr = tr->tail();
  }
  return true;
}


void VarOrder::order_diff_helper(VarOrder& vo, const List<Edge>* edges, Stack<VarOrder>& res)
{
  if (List<Edge>::isEmpty(edges)) {
    return;
  }

  auto e = edges->head();

  switch (e.c) {
    case PoComp::GT:
      if (vo.query(e.x,e.y) != PoComp::GT) {
        VarOrder eq = vo;
        VarOrder lt = vo;
        ALWAYS(eq.add_eq(e.x,e.y));
        ALWAYS(lt.add_gt(e.y,e.x));
        res.push(eq);
        res.push(lt);
        ALWAYS(vo.add_gt(e.x,e.y));
      }
      break;
    case PoComp::EQ:
      if (vo.query(e.x,e.y) != PoComp::EQ) {
        VarOrder gt = vo;
        VarOrder lt = vo;
        ALWAYS(gt.add_gt(e.x,e.y));
        ALWAYS(lt.add_gt(e.y,e.x));
        res.push(gt);
        res.push(lt);
        ALWAYS(vo.add_eq(e.x,e.y));
      }
      break;
    default:
      ASSERTION_VIOLATION;
  }

  order_diff_helper(vo, edges->tail(), res);
}

Stack<VarOrder> VarOrder::order_diff(const VarOrder& vo, const VarOrder& other)
{
  return order_diff_nonrecursive(vo,other);
  // auto tr = other.transitive_reduction();

  // Stack<VarOrder> res;
  // VarOrder temp = vo;
  // order_diff_helper(temp, tr, res);
  // return res;
}

Stack<VarOrder> VarOrder::order_diff_nonrecursive(const VarOrder& vo, const VarOrder& other)
{
  auto tr = other.transitive_reduction();

  Stack<VarOrder> res;
  VarOrder temp = vo;

  while (List<Edge>::isNonEmpty(tr)) {

    auto e = tr->head();

    switch (e.c) {
      case PoComp::GT:
        if (temp.query(e.x,e.y) != PoComp::GT) {
          VarOrder eq = temp;
          VarOrder lt = temp;
          ALWAYS(eq.add_eq(e.x,e.y));
          ALWAYS(lt.add_gt(e.y,e.x));
          res.push(eq);
          res.push(lt);
          ALWAYS(temp.add_gt(e.x,e.y));
        }
        break;
      case PoComp::EQ:
        if (temp.query(e.x,e.y) != PoComp::EQ) {
          VarOrder gt = temp;
          VarOrder lt = temp;
          ALWAYS(gt.add_gt(e.x,e.y));
          ALWAYS(lt.add_gt(e.y,e.x));
          res.push(gt);
          res.push(lt);
          ALWAYS(temp.add_eq(e.x,e.y));
        }
        break;
      default:
        ASSERTION_VIOLATION;
    }

    tr = tr->tail();
  }

  return res;
}

// bitvector operations

void setBit(unsigned x, unsigned y, PoComp c, VarOrderBV& bv)
{
  if (x > 6 || y > 6) {
    return;
  }
  ASS(c!=PoComp::INC);
  if (x > y) {
    swap(x,y);
    c = reverse(c);
  }
  size_t idx = y*(y-1)/2 + x;
  size_t pos;
  switch (c) {
    case PoComp::GT:
      pos = 3*idx;
      break;
    case PoComp::EQ:
      pos = 3*idx+1;
      break;
    case PoComp::LT:
      pos = 3*idx+2;
      break;
    case PoComp::INC:
      return;
  }
  bv |= 1UL << pos;
}

void unsetBit(unsigned x, unsigned y, PoComp c, VarOrderBV& bv)
{
  if (x > 6 || y > 6) {
    return;
  }
  ASS(c!=PoComp::INC);
  if (x > y) {
    swap(x,y);
    c = reverse(c);
  }
  size_t idx = y*(y-1)/2 + x;
  size_t pos;
  switch (c) {
    case PoComp::GT:
      pos = 3*idx;
      break;
    case PoComp::EQ:
      pos = 3*idx+1;
      break;
    case PoComp::LT:
      pos = 3*idx+2;
      break;
    case PoComp::INC:
      return;
  }
  bv &= ~(1UL << pos);
}

bool isBitSet(unsigned x, unsigned y, PoComp c, VarOrderBV bv)
{
  if (x > 6 || y > 6) {
    return false;
  }
  ASS(c!=PoComp::INC);
  if (x > y) {
    swap(x,y);
    c = reverse(c);
  }
  size_t idx = y*(y-1)/2 + x;
  size_t pos;
  switch (c) {
    case PoComp::GT:
      pos = 3*idx;
      break;
    case PoComp::EQ:
      pos = 3*idx+1;
      break;
    case PoComp::LT:
      pos = 3*idx+2;
      break;
    case PoComp::INC:
      return false;
  }
  return (bv & (1UL << pos));
}

// ~000 & 111 -> 111 & 111 -> 1
// ~001 & 111 -> 110 & 111 -> 1
// ...
// ~111 & 111 -> 000 & 111 -> 0

bool isReducedUnderAny(VarOrderBV bv)
{
  for (unsigned i = 0; i < 21; i++) {
    size_t pos = 3*i;
    if (!(~bv & (0b111UL << pos))) {
      return true;
    }
  }
  return false;
}

VarOrderBV getRemaining(VarOrderBV bv)
{
  return ~bv & ~(1UL << 63);
}

PoComp oneRemains(VarOrderBV val, unsigned x, unsigned y)
{
  ASS(x <= 6 && y <= 6);
  ASS(x < y);
  size_t idx = y*(y-1)/2 + x;
  bool gt = val & (1UL << (3*idx));
  bool eq = val & (1UL << (3*idx+1));
  bool lt = val & (1UL << (3*idx+2));
  ASS(!gt || !eq || !lt);
  if (gt && eq) {
    return PoComp::LT;
  }
  if (gt && lt) {
    return PoComp::EQ;
  }
  if (eq && lt) {
    return PoComp::GT;
  }
  return PoComp::INC;
}

bool addToVo(VarOrder& vo, unsigned x, unsigned y, PoComp c)
{
  ASS(x <= 6 && y <= 6);
  switch (c) {
    case PoComp::GT:
      return vo.add_gt(x,y);
    case PoComp::EQ:
      return vo.add_eq(x,y);
    case PoComp::LT:
      return vo.add_gt(y,x);
  }
  return true;
}

bool isRemainingUnsat(VarOrderBV val)
{
  for (unsigned i = 0; i < 6; i++) {
    for (unsigned j = i+1; j < 6; j++) {
      auto c0 = oneRemains(val,i,j);
      if (c0 == PoComp::INC) {
        continue;
      }
      for (unsigned l = j+1; l < 6; l++) {
        auto c1 = oneRemains(val,i,l);
        auto c2 = oneRemains(val,j,l);
        if (c1 == PoComp::INC || c2 == PoComp::INC) {
          continue;
        }
        VarOrder vo;
        if (!addToVo(vo,i,j,c0)) {
          return true;
        }
        if (!addToVo(vo,i,l,c1)) {
          return true;
        }
        if (!addToVo(vo,j,l,c2)) {
          return true;
        }
      }
    }
  }
  return false;
}


}