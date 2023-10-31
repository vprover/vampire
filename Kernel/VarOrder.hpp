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
  VirtualIterator<std::tuple<const unsigned&,const unsigned&,PoComp>> iter_relations() const;
  size_t rel_size() const;
  bool subseteq(const VarOrder& other) const;

  class EqApplicator
  {
  public:
    EqApplicator(const VarOrder& vo) : _vo(vo) {}
    TermList apply(unsigned v);

  private:
    const VarOrder& _vo;
  };

private:
  PartialOrdering<unsigned> _po;
};

// using namespace Lib;

// class VarOrder;

// using VarOrders = Stack<VarOrder>;

// class VarOrder
// {
// public:
//   enum Comp {
//     UNSET=0,
//     EQ=1,
//     GT=2,
//     LT=3,
//   };
//   VarOrder(const DHSet<unsigned>& vars)
//   : _vars(), _edges(0) {
//     // if (vars.size()) {
//     //   _edges = new TriangularArray<Comp>(vars.size());
//     // }
//     DHSet<unsigned>::Iterator vit(vars);
//     unsigned cnt = 0;
//     while (vit.hasNext()) {
//       ALWAYS(_vars.insert(vit.next(),cnt++));
//     }
//   }
//   VarOrder(const VarOrder& vo)
//     : _vars(vo._vars), _edges(0) {
//     if (numVars()) {
//       _edges = new TriangularArray<Comp>(numVars());
//       for (unsigned i = 0; i < _vars.size(); i++) {
//         for (unsigned j = i; j < _vars.size(); j++) {
//           _edges->set(j,i,vo._edges->get(j,i));
//         }
//       }
//     }
//   }
//   ~VarOrder() {
//     // if (_edges) {
//     //   delete _edges;
//     // }
//   }

//   void setEdges(TriangularArray<Comp>* edges) { _edges = edges; }
//   size_t numVars() const { return _vars.size(); }
//   VirtualIterator<unsigned> iterVars() const {
//     return _vars.domain();
//   }
//   bool hasVar(unsigned v) const { return _vars.find(v); }
//   bool add_gt(unsigned x, unsigned y);
//   bool add_eq(unsigned x, unsigned y);
//   void infer_transitive();
//   void complete_edge(unsigned i, unsigned j, unsigned k);

//   Comp val(unsigned x, unsigned y) const;
//   void set_val(unsigned x, unsigned y, Comp val);
//   Comp get(unsigned x, unsigned y) const;
//   void set(unsigned x, unsigned y, Comp val);

//   static VarOrder transitive_reduction(const VarOrder& vo);
//   static VarOrders order_diff(const VarOrders& vos, const VarOrders& others);
//   // static void order_diff(const VarOrder& vo, const VarOrders& others, VarOrders& res);
//   static VarOrders all(const DHSet<unsigned>& vars) {
//     VarOrders res;
//     res.push(VarOrder(vars));
//     return res;
//   }
//   static bool makeEqual(TermList tl1, TermList tl2, VarOrder& vo);
//   static bool getVarOrder(unsigned size, unsigned i, VarOrder& vo);

//   void expand(unsigned x, unsigned y);

//   friend std::ostream& operator<<(std::ostream& out, const VarOrder& vo);
//   friend bool operator==(const VarOrder& vo1, const VarOrder& vo2);

// private:
//   DHMap<unsigned,unsigned> _vars;
//   TriangularArray<Comp>* _edges;
// };

// std::ostream& operator<<(std::ostream& out, const VarOrder& vo);

// bool operator==(const VarOrder& vo1, const VarOrder& vo2);
// bool contains(const VarOrders& vos, const VarOrder& vo);

// class VarOrderEqApplicator
// {
// public:
//   VarOrderEqApplicator(const VarOrder& vo) : _vo(vo) {}
//   TermList apply(unsigned v);

// private:
//   const VarOrder& _vo;
// };

}

#endif