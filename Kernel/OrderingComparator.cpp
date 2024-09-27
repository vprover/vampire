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
    case OrderingComparator::BranchTag::T_RESULT:
      out << "r";
      break;
    case OrderingComparator::BranchTag::T_COMPARISON:
      out << "c";
      break;
    case OrderingComparator::BranchTag::T_WEIGHT:
      out << "w";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& out, const OrderingComparator::Branch& branch)
{
  out << branch._tag() << (branch._ready()?" ":"? ");
  switch (branch._tag()) {
    case OrderingComparator::BranchTag::T_RESULT: {
      auto n = branch._node();
      if (n) {
        out << n->data << " ";
      } else {
        out << "0x0 ";
      }
      break;
    }
    case OrderingComparator::BranchTag::T_WEIGHT: {
      auto n = branch._node();
      out << n->w << " ";
      for (const auto& [var, coeff] : *n->varCoeffPairs) {
        out << "X" << var << " " << coeff << " ";
      }
      break;
    }
    case OrderingComparator::BranchTag::T_COMPARISON: {
      auto n = branch._node();
      out << n->lhs << " " << n->rhs;
      break;
    }
  }
  return out;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator& comp)
{
  Stack<std::pair<const OrderingComparator::Branch*, unsigned>> todo;
  todo.push(std::make_pair(&comp._root,0));
  // Note: using this set we get a more compact representation
  // DHSet<OrderingComparator::Node*> seen;

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    for (unsigned i = 0; i < kv.second; i++) {
      if (i+1 == kv.second) {
        str << "  |--";
      } else {
        str << "  |  ";
      }
    }
    str << *kv.first << std::endl;
    if (kv.first->_node()/*  && seen.insert(kv.first->n.ptr()) */) {
      switch (kv.first->_tag()) {
        case OrderingComparator::BranchTag::T_RESULT: {
          todo.push(std::make_pair(&kv.first->_node()->alternative,kv.second+1));
          break;
        }
        default: {
          todo.push(std::make_pair(&kv.first->_node()->incBranch,kv.second+1));
          todo.push(std::make_pair(&kv.first->_node()->gtBranch,kv.second+1));
          todo.push(std::make_pair(&kv.first->_node()->eqBranch,kv.second+1));
          break;
        }
      }
    }
  }
  return str;
}

OrderingComparator::OrderingComparator(const Ordering& ord, const Stack<Ordering::Constraint>& comps, void* result)
: _ord(ord), _root(), _curr(&_root)
{
  ASS(result);
  auto curr = &_root;
  for (const auto& [lhs,rhs,rel] : comps) {
    *curr = OrderingComparator::Branch(lhs, rhs);
    curr = &curr->_node()->getBranch(rel);
  }
  *curr = Branch(result, Branch());
}

OrderingComparator::~OrderingComparator() = default;

void* OrderingComparator::next(const SubstApplicator* applicator)
{
  ASS(_curr);
  while (_curr->_node()) {
    expand();
    ASS(_curr->_ready());
    auto node = _curr->_node();

    if (_curr->_tag() == BranchTag::T_RESULT) {
      if (node) {
        _curr = &node->alternative;
        return node->data;
      }
      return nullptr;
    }

    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (_curr->_tag() == BranchTag::T_COMPARISON) {

      comp = _ord.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
      _cache.push({ node->lhs, node->rhs, comp });

    } else {
      ASS(_curr->_tag() == BranchTag::T_WEIGHT);

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
    _curr = &_curr->_node()->getBranch(comp);
  }
  return nullptr;
}

void OrderingComparator::addAlternative(const OrderingComparator& other)
{
  auto& branch = other._root;
  ASS(!branch._ready()); // branch should be unexpanded

  static unsigned ts = 0;
  ts++;

  static Stack<std::pair<Branch*,Branch>> todo;
  todo.reset();

  auto pushBranches = [](Branch* b, const Branch& other) {
    // if other branch is unsuccessful, do nothing
    if (other._tag() == BranchTag::T_RESULT && !other._node()) {
      return;
    }
    // if this branch is unsuccessful, replace this with other
    if (b->_tag() == BranchTag::T_RESULT && !b->_node()) {
      *b = other;
      return;
    }
    todo.push(std::make_pair(b,other));
  };

  pushBranches(&_root, branch);

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    auto currB = kv.first;
    auto otherB = kv.second;
    ASS(currB->_node());
    ASS(otherB._node());
    // if we already checked this branch, continue
    if (currB->_node()->ts == ts) {
      continue;
    }
    currB->_node()->ts = ts;
    if (currB->_tag() == BranchTag::T_RESULT) {
      pushBranches(&currB->_node()->alternative, otherB);
      continue;
    }
    // TODO: results should be only pushed down
    // in this case onto successful branches
    //
    // if (currB->tag == BranchTag::T_UNKNOWN && currB->tag != BranchTag::T_COMPARISON) {
    //   // both must be comparison nodes
    //   auto n = static_cast<ComparisonNode*>(currB->n.ptr());
    //   auto o = static_cast<ComparisonNode*>(otherB.n.ptr());
    //   if (n->lhs == o->lhs && n->rhs == o->rhs) {
    //     pushBranches(&currB->n->eqBranch, otherB.n->eqBranch);
    //     pushBranches(&currB->n->gtBranch, otherB.n->gtBranch);
    //     pushBranches(&currB->n->incBranch, otherB.n->incBranch);
    //     continue;
    //   }
    // }
    pushBranches(&currB->_node()->eqBranch, otherB);
    pushBranches(&currB->_node()->gtBranch, otherB);
    pushBranches(&currB->_node()->incBranch, otherB);
  }
}

void OrderingComparator::expand()
{
  while (!_curr->_ready())
  {
    // take temporary ownership of node
    Branch nodeHolder = *_curr;
    auto node = nodeHolder._node();

    if (_curr->_tag() == BranchTag::T_RESULT) {
      *_curr = Branch(node->data, node->alternative);
      _curr->_setReady(true);
      return;
    }
    ASS(_curr->_tag() != BranchTag::T_WEIGHT);

    // Use compare here to filter out as many
    // precomputable comparisons as possible.
    auto comp = _ord.compare(node->lhs,node->rhs);
    if (comp != Ordering::INCOMPARABLE) {
      if (comp == Ordering::LESS) {
        *_curr = node->incBranch;
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
  ASS(!_curr->_ready());
  _curr->_setReady(true);
}

bool OrderingComparator::tryExpandVarCase()
{
  // take temporary ownership of node
  Branch nodeHolder = *_curr;
  auto node = nodeHolder._node();

  // If we have a variable, we cannot preprocess further.
  if (!node->lhs.isVar() && !node->rhs.isVar()) {
    return false;
  }
  // try cache
  for (const auto& [s,t,r] : _cache) {
    if (s == node->lhs && t == node->rhs) {
      if (r == Ordering::GREATER) {
        *_curr = node->gtBranch;
      } else if (r == Ordering::EQUAL) {
        *_curr = node->eqBranch;
      } else {
        ASS_EQ(r, Ordering::INCOMPARABLE);
        *_curr = node->incBranch;
      }
      return true;
    }

    if (s == node->rhs && t == node->lhs && r != Ordering::INCOMPARABLE) {
      if (r == Ordering::GREATER) {
        *_curr = node->incBranch;
      } else {
        ASS_EQ(r, Ordering::EQUAL);
        *_curr = node->eqBranch;
      }
      // Note: since we use isGreater which results
      // in INCOMPARABLE when compare would be LESS,
      // the INCOMPARABLE result we cannot use here
      return true;
    }
  }
  // make a fresh copy
  *_curr = Branch(node->lhs, node->rhs);
  _curr->_node()->eqBranch = node->eqBranch;
  _curr->_node()->gtBranch = node->gtBranch;
  _curr->_node()->incBranch = node->incBranch;
  _curr->_setReady(true);
  return true;
}

void OrderingComparator::Node::incRefCnt()
{
  refcnt++;
}

void OrderingComparator::Node::decRefCnt()
{
  ASS(refcnt);
  refcnt--;
  if (!refcnt) {
    delete this;
  }
}

}