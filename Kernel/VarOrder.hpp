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
 * @file VarOrder.hpp
 */

#ifndef __VarOrder__
#define __VarOrder__

#include "PartialOrdering.hpp"

namespace Kernel {

class VarOrder {
public:
  bool add_gt(unsigned x, unsigned y);
  bool add_eq(unsigned x, unsigned y);
  PoComp query(unsigned x, unsigned y) const;
  bool is_total(size_t n) const;
  vstring to_string() const;
  const List<Edge>* transitive_reduction() const;
  bool is_empty() const;
  size_t size() const { return _po.size(); }
  VirtualIterator<std::tuple<unsigned,unsigned,PoComp>> iter_relations() const;
  size_t rel_size() const;
  bool subseteq(const VarOrder& other) const;
  bool tryExtendWith(const VarOrder& other);

  class EqApplicator
  {
  public:
    EqApplicator(const VarOrder& vo) : _vo(vo) {}
    TermList apply(unsigned v);

  private:
    const VarOrder& _vo;
  };

  static void order_diff_helper(VarOrder& vo, const List<Edge>* edges, Stack<VarOrder>& res);
  static Stack<VarOrder> order_diff(const VarOrder& vo, const VarOrder& other);
  static Stack<VarOrder> order_diff_nonrecursive(const VarOrder& vo, const VarOrder& other);

private:
  PartialOrdering<unsigned> _po;
};

void setBit(unsigned x, unsigned y, PoComp c, VarOrderBV& val);
void unsetBit(unsigned x, unsigned y, PoComp c, VarOrderBV& val);
bool isBitSet(unsigned x, unsigned y, PoComp c, VarOrderBV val);
bool isReducedUnderAny(VarOrderBV val);
VarOrderBV getRemaining(VarOrderBV val);
PoComp oneRemains(VarOrderBV val, unsigned x, unsigned y);
bool addToVo(VarOrder& vo, unsigned x, unsigned y, PoComp c);
bool isRemainingUnsat(VarOrderBV val);

}

#endif