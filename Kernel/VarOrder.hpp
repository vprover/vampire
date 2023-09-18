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

#include "Lib/DHSet.hpp"
#include "Lib/Stack.hpp"
#include "Lib/TriangularArray.hpp"

// #include "TermIterators.hpp"

#include "Term.hpp"

namespace Kernel {

using namespace Lib;

struct VarOrder;

using VarOrders = Stack<VarOrder>;

struct VarOrder
{
  VarOrder() : _vars(10), _edges(_vars) {}
  VarOrder(const VarOrder& vo)
    : _vars(vo._vars), _edges(vo._vars) {
    for (unsigned i = 0; i < _vars; i++) {
      for (unsigned j = i; j < _vars; j++) {
        _edges.set(j,i,vo._edges.get(j,i));
      }
    }
  }

  bool add_gt(unsigned x, unsigned y);
  bool add_eq(unsigned x, unsigned y);
  void infer_transitive();
  void complete_edge(unsigned i, unsigned j, unsigned k);

  enum Comp {
    UNSET=0,
    EQ=1,
    GT=2,
    LT=3,
  };

  Comp val(unsigned x, unsigned y) const;
  void set_val(unsigned x, unsigned y, Comp val);

  static VarOrder transitive_reduction(const VarOrder& vo);
  static VarOrders order_diff(const VarOrders& vos, const VarOrders& others);
  // static void order_diff(const VarOrder& vo, const VarOrders& others, VarOrders& res);
  static VarOrders all() {
    VarOrders res;
    res.push(VarOrder());
    return res;
  }
  static bool makeEqual(TermList tl1, TermList tl2, VarOrder& vo);

  void expand(unsigned x, unsigned y);

  size_t _vars;
  TriangularArray<Comp> _edges;
};

std::ostream& operator<<(std::ostream& out, const VarOrder& vo);

bool operator==(const VarOrder& vo1, const VarOrder& vo2);
bool contains(const VarOrders& vos, const VarOrder& vo);

class VarOrderEqApplicator
{
public:
  VarOrderEqApplicator(const VarOrder& vo) : _vo(vo) {}
  TermList apply(unsigned v) {
    if (v >= _vo._vars) {
      return TermList(v,false);
    }
    for (unsigned i = 0; i < v; i++) {
      if (_vo.val(i,v)==VarOrder::EQ) {
        return TermList(i,false);
      }
    }
    return TermList(v,false);
  }

private:
  const VarOrder& _vo;
};

}

#endif