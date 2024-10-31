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
 * @file OrderingComparator.cpp
 * Implements class OrderingComparator.
 */

#include "Lib/Stack.hpp"
#include "Lib/Environment.hpp"

#include "KBO.hpp"
#include "SubstHelper.hpp"

#include "OrderingComparator.hpp"

using namespace std;

namespace Kernel {

std::ostream& operator<<(std::ostream& out, const OrderingComparator::BranchTag& t)
{
  switch (t) {
    case OrderingComparator::BranchTag::T_DATA:
      out << "r";
      break;
    case OrderingComparator::BranchTag::T_TERM:
      out << "c";
      break;
    case OrderingComparator::BranchTag::T_POLY:
      out << "w";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const OrderingComparator::Node& node)
{
  out << (OrderingComparator::BranchTag)node.tag << (node.ready?" ":"? ");
  switch (node.tag) {
    case OrderingComparator::BranchTag::T_DATA: {
      out << node.data;
      break;
    }
    case OrderingComparator::BranchTag::T_POLY: {
      out << node.w << " ";
      for (const auto& [var, coeff] : *node.varCoeffPairs) {
        out << "X" << var << " " << coeff << " ";
      }
      break;
    }
    case OrderingComparator::BranchTag::T_TERM: {
      out << node.lhs << " " << node.rhs;
      break;
    }
  }
  return out;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator& comp)
{
  Stack<std::pair<const OrderingComparator::Branch*, unsigned>> todo;
  todo.push(std::make_pair(&comp._source,0));
  // Note: using this set we get a more compact representation
  DHSet<OrderingComparator::Node*> seen;

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    for (unsigned i = 0; i < kv.second; i++) {
      if (i+1 == kv.second) {
        str << "  |--";
      } else {
        str << "  |  ";
      }
    }
    str << *kv.first->node() << std::endl;
    if (seen.insert(kv.first->node())) {
      if (kv.first->node()->tag==OrderingComparator::BranchTag::T_DATA) {
        if (kv.first->node()->data) {
          todo.push(std::make_pair(&kv.first->node()->alternative,kv.second+1));
        }
      } else {
        todo.push(std::make_pair(&kv.first->node()->ngeBranch,kv.second+1));
        todo.push(std::make_pair(&kv.first->node()->gtBranch,kv.second+1));
        todo.push(std::make_pair(&kv.first->node()->eqBranch,kv.second+1));
      }
    }
  }
  return str;
}

OrderingComparator::OrderingComparator(const Ordering& ord, const Stack<Ordering::Constraint>& comps, void* result)
: _ord(ord), _source(), _sink(nullptr, Branch()), _curr(&_source), _prev(nullptr)
{
  ASS(result);
  static Ordering::Result ordVals[] = { Ordering::EQUAL, Ordering::GREATER, Ordering::INCOMPARABLE };
  auto curr = &_source;
  for (const auto& [lhs,rhs,rel] : comps) {
    *curr = OrderingComparator::Branch(lhs, rhs);
    for (unsigned i = 0; i < 3; i++) {
      if (ordVals[i] != comps[0].rel) {
        curr->node()->getBranch(ordVals[i]) = _sink;
      }
    }
    curr = &curr->node()->getBranch(rel);
  }
  *curr = Branch(result, _sink);
  _sink.node()->ready = true;
}

OrderingComparator::~OrderingComparator() = default;

void* OrderingComparator::next(const SubstApplicator* applicator)
{
  ASS(_curr);
  for (;;) {
    expand();
    auto node = _curr->node();
    ASS(node->ready);

    if (node->tag == BranchTag::T_DATA) {
      if (!node->data) {
        return nullptr;
      }
      _prev = _curr;
      _curr = &node->alternative;
      return node->data;
    }

    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (node->tag == BranchTag::T_TERM) {

      comp = _ord.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
      // _trace.set({ node->lhs, node->rhs, comp });

    } else {
      ASS(node->tag == BranchTag::T_POLY);

      const auto& kbo = static_cast<const KBO&>(_ord);
      auto weight = node->w;
      ZIArray<int> varDiffs;
      for (const auto& [var, coeff] : *node->varCoeffPairs) {
        AppliedTerm tt(TermList::var(var), applicator, true);

        VariableIterator vit(tt.term);
        while (vit.hasNext()) {
          auto v = vit.next();
          varDiffs[v.var()] += coeff;
          // since the counts are sorted in descending order,
          // this can only mean we will fail
          if (varDiffs[v.var()]<0) {
            goto loop_end;
          }
        }
        int64_t w = kbo.computeWeight(tt);
        weight += coeff*w;
        // due to descending order of counts,
        // this also means failure
        if (coeff<0 && weight<0) {
          goto loop_end;
        }
      }

      if (weight > 0) {
        comp = Ordering::GREATER;
      } else if (weight == 0) {
        comp = Ordering::EQUAL;
      }
    }
loop_end:
    _prev = _curr;
    _curr = &node->getBranch(comp);
  }
  return nullptr;
}

void OrderingComparator::insert(const Stack<Ordering::Constraint>& comps, void* result)
{
  ASS(result);
  static Ordering::Result ordVals[] = { Ordering::EQUAL, Ordering::GREATER, Ordering::INCOMPARABLE };
  // we mutate current fail node and add a new one
  auto curr = &_sink;
  Branch newFail(nullptr, Branch());
  newFail.node()->ready = true;

  curr->node()->~Node();
  curr->node()->ready = false;

  if (comps.isNonEmpty()) {
    curr->node()->tag = T_TERM;
    curr->node()->lhs = comps[0].lhs;
    curr->node()->rhs = comps[0].rhs;
    for (unsigned i = 0; i < 3; i++) {
      if (ordVals[i] != comps[0].rel) {
        curr->node()->getBranch(ordVals[i]) = newFail;
      }
    }
    curr = &curr->node()->getBranch(comps[0].rel);
    for (unsigned i = 1; i < comps.size(); i++) {
      auto [lhs,rhs,rel] = comps[i];
      *curr = OrderingComparator::Branch(lhs, rhs);
      for (unsigned i = 0; i < 3; i++) {
        if (ordVals[i] != rel) {
          curr->node()->getBranch(ordVals[i]) = newFail;
        }
      }
      curr = &curr->node()->getBranch(rel);
    }
    *curr = Branch(result, newFail);
  } else {
    curr->node()->tag = T_DATA;
    curr->node()->data = result;
    curr->node()->alternative = newFail;
  }

  _sink = newFail;
}

void OrderingComparator::expand()
{
  ASS(_curr->node());
  while (!_curr->node()->ready)
  {
    auto node = _curr->node();

    if (node->tag == BranchTag::T_DATA) {
      ASS(node->data); // no fail nodes here
      // if refcnt > 1 we copy the node and
      // we can also safely use the original
      if (node->refcnt > 1) {
        *_curr = Branch(node->data, node->alternative);
      }
      _curr->node()->trace = getCurrentTrace().release();
      _curr->node()->ready = true;
      return;
    }
    if (node->tag == BranchTag::T_POLY) {
      auto trace = getCurrentTrace();
      // if refcnt > 1 we copy the node and
      // we can also safely use the original
      if (node->refcnt > 1) {
        auto varCoeffPairs = new Stack<VarCoeffPair>(*node->varCoeffPairs);
        *_curr = Branch(node->w, varCoeffPairs);
        _curr->node()->eqBranch = node->eqBranch;
        _curr->node()->gtBranch = node->gtBranch;
        _curr->node()->ngeBranch = node->ngeBranch;
      }
      _curr->node()->trace = trace.release();
      _curr->node()->ready = true;
      return;
    }

    // Use compare here to filter out as many
    // precomputable comparisons as possible.
    auto comp = _ord.compare(node->lhs,node->rhs);
    if (comp != Ordering::INCOMPARABLE) {
      if (comp == Ordering::LESS) {
        *_curr = node->ngeBranch;
      } else if (comp == Ordering::GREATER) {
        *_curr = node->gtBranch;
      } else {
        *_curr = node->eqBranch;
      }
      continue;
    }
    // If we have a variable, we cannot preprocess further.
    if (tryExpandVarCase()) {
      continue;
    }

    expandTermCase();
  }
}

void OrderingComparator::expandTermCase()
{
  ASS(_curr->node() && !_curr->node()->ready);
  _curr->node()->ready = true;
}

bool OrderingComparator::tryExpandVarCase()
{
  auto node = _curr->node();

  // If we have a variable, we cannot preprocess further.
  if (!node->lhs.isVar() && !node->rhs.isVar()) {
    return false;
  }
  auto trace = getCurrentTrace();
  Ordering::Result val;
  if (trace->get(node->lhs, node->rhs, val)) {
    if (val == Ordering::GREATER) {
      *_curr = node->gtBranch;
    } else if (val == Ordering::EQUAL) {
      *_curr = node->eqBranch;
    } else {
      *_curr = node->ngeBranch;
    }
    return true;
  }
  // TODO eventually incorporate this into the Trace
  if (node->lhs.isVar() && node->rhs.isTerm()) {
    SubtermIterator sti(node->rhs.term());
    while (sti.hasNext()) {
      auto st = sti.next();
      if (trace->get(node->lhs, st, val)) {
        if (val == Ordering::INCOMPARABLE) {
          *_curr = node->ngeBranch;
          return true;
        } else if (val == Ordering::LESS) {
          *_curr = node->ngeBranch;
          return true;
        }
      }
    }
  }
  // if refcnt > 1 we copy the node and
  // we can also safely use the original
  if (node->refcnt > 1) {
    *_curr = Branch(node->lhs, node->rhs);
    _curr->node()->eqBranch = node->eqBranch;
    _curr->node()->gtBranch = node->gtBranch;
    _curr->node()->ngeBranch = node->ngeBranch;
  }
  _curr->node()->ready = true;
  _curr->node()->trace = trace.release();
  return true;
}

ScopedPtr<OrderingComparator::Trace> OrderingComparator::getCurrentTrace()
{
  ASS(!_curr->node()->ready);

  if (!_prev) {
    return ScopedPtr<Trace>(new Trace());
  }

  ASS(_prev->node()->ready);
  ASS(_prev->node()->trace);

  switch (_prev->node()->tag) {
    case BranchTag::T_TERM: {
      auto trace = new Trace(*_prev->node()->trace);
      auto lhs = _prev->node()->lhs;
      auto rhs = _prev->node()->rhs;
      Ordering::Result res;
      if (_curr == &_prev->node()->eqBranch) {
        res = Ordering::EQUAL;
      } else if (_curr == &_prev->node()->gtBranch) {
        res = Ordering::GREATER;
      } else {
        res = Ordering::INCOMPARABLE;
      }
      ALWAYS(trace->set({ lhs, rhs, res }));
      ASS(lhs.isVar() || rhs.isVar());
      if (res == Ordering::INCOMPARABLE) {
        if (lhs.isTerm()) {
          SubtermIterator stit(lhs.term());
          while (stit.hasNext()) {
            trace->set({ stit.next(), rhs, Ordering::INCOMPARABLE });
          }
        }
      } else {
        if (rhs.isTerm()) {
          SubtermIterator stit(rhs.term());
          while (stit.hasNext()) {
            trace->set({ lhs, stit.next(), Ordering::GREATER });
          }
        }
      }
      return ScopedPtr<Trace>(trace);
    }
    case BranchTag::T_DATA: {
      return ScopedPtr<Trace>(new Trace(*_prev->node()->trace));
    }
    case BranchTag::T_POLY: {
      return ScopedPtr<Trace>(new Trace(*_prev->node()->trace));
    }
  }
  ASSERTION_VIOLATION;
}

OrderingComparator::Branch::~Branch()
{
  setNode(nullptr);
}

OrderingComparator::Branch::Branch(const Branch& other)
{
  setNode(other._node);
}

OrderingComparator::Branch& OrderingComparator::Branch::operator=(const Branch& other)
{
  if (&other==this) {
    return *this;
  }
  setNode(other.node());
  return *this;
}

OrderingComparator::Branch::Branch(Branch&& other)
  : _node(other._node)
{
  other._node = nullptr;
}

OrderingComparator::Branch& OrderingComparator::Branch::operator=(Branch&& other)
{
  if (&other==this) {
    return *this;
  }
  swap(_node,other._node);
  return *this;
}

OrderingComparator::Node::~Node()
{
  switch(tag) {
    case T_DATA:
      alternative.~Branch();
      break;
    case T_TERM:
      break;
    case T_POLY:
      delete varCoeffPairs;
      break;
  }
  ready = false;
  delete trace;
  trace = nullptr;
}

void OrderingComparator::Node::incRefCnt()
{
  refcnt++;
}

void OrderingComparator::Node::decRefCnt()
{
  ASS(refcnt>=0);
  refcnt--;
  if (refcnt==0) {
    delete this;
  }
}

}
