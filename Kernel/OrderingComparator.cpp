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
#include "KBO.hpp"

#include "SubstHelper.hpp"

#include "OrderingComparator.hpp"

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
  out << branch.tag << (branch.ready?" ":"? ");
  switch (branch.tag) {
    case OrderingComparator::BranchTag::T_RESULT: {
      auto n = static_cast<OrderingComparator::ResultNode*>(branch.n.ptr());
      if (n) {
        out << n->data << " ";
      } else {
        out << "0x0 ";
      }
      break;
    }
    case OrderingComparator::BranchTag::T_WEIGHT: {
      auto n = static_cast<OrderingComparator::WeightNode*>(branch.n.ptr());
      out << n->w << " ";
      for (const auto& [var, coeff] : n->varCoeffPairs) {
        out << "X" << var << " " << coeff << " ";
      }
      break;
    }
    case OrderingComparator::BranchTag::T_COMPARISON: {
      auto n = static_cast<OrderingComparator::ComparisonNode*>(branch.n.ptr());
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
    str << *kv.first << std::endl;
    if (kv.first->n/*  && seen.insert(kv.first->n.ptr()) */) {
      switch (kv.first->tag) {
        case OrderingComparator::BranchTag::T_RESULT: {
          auto n = static_cast<const OrderingComparator::ResultNode*>(kv.first->n.ptr());
          todo.push(std::make_pair(&n->alternative,kv.second+1));
          break;
        }
        default: {
          todo.push(std::make_pair(&kv.first->n->incBranch,kv.second+1));
          todo.push(std::make_pair(&kv.first->n->gtBranch,kv.second+1));
          todo.push(std::make_pair(&kv.first->n->eqBranch,kv.second+1));
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
    curr = &curr->n->getBranch(rel);
  }
  *curr = Branch(result);
}

OrderingComparator::~OrderingComparator() = default;

void* OrderingComparator::next(const SubstApplicator* applicator)
{
  ASS(_curr);
  while (_curr->n) {
    expand();
    ASS(_curr->ready);

    if (_curr->tag == BranchTag::T_RESULT) {
      if (_curr && _curr->n) {
        auto node = static_cast<ResultNode*>(_curr->n.ptr());
        _curr = &node->alternative;
        return node->data;
      }
      return nullptr;
    }

    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (_curr->tag == BranchTag::T_COMPARISON) {

      auto node = static_cast<ComparisonNode*>(_curr->n.ptr());
      comp = _ord.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
      _cache.push({ node->lhs, node->rhs, comp });

    } else {
      ASS(_curr->tag == BranchTag::T_WEIGHT);

      const auto& kbo = static_cast<const KBO&>(_ord);
      auto node = static_cast<WeightNode*>(_curr->n.ptr());
      auto weight = node->w;
      ZIArray<int> varDiffs;
      for (const auto& [var, coeff] : node->varCoeffPairs) {
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
        auto w = kbo.computeWeight(tt);
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
    _curr = &_curr->n->getBranch(comp);
  }
  return nullptr;
}

void OrderingComparator::addAlternative(const OrderingComparator& other)
{
  auto& branch = other._root;
  ASS(!branch.ready); // branch should be unexpanded

  static unsigned ts = 0;
  ts++;

  static Stack<std::pair<Branch*,Branch>> todo;
  todo.reset();

  auto pushBranches = [](Branch* b, const Branch& other) {
    // if other branch is unsuccessful, do nothing
    if (other.tag == BranchTag::T_RESULT && !other.n) {
      return;
    }
    // if this branch is unsuccessful, replace this with other
    if (b->tag == BranchTag::T_RESULT && !b->n) {
      *b = other;
      return;
    }
    todo.push(std::make_pair(b,other));
  };

  pushBranches(&_root, branch);

  while (todo.isNonEmpty()) {
    auto [currB, otherB] = todo.pop();
    ASS(currB->n);
    ASS(otherB.n);
    // if we already checked this branch, continue
    if (currB->n->getTs()==ts) {
      continue;
    }
    currB->n->setTs(ts);
    if (currB->tag == BranchTag::T_RESULT) {
      auto n = static_cast<ResultNode*>(currB->n.ptr());
      pushBranches(&n->alternative, otherB);
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
    pushBranches(&currB->n->eqBranch, otherB);
    pushBranches(&currB->n->gtBranch, otherB);
    pushBranches(&currB->n->incBranch, otherB);
  }
}

void OrderingComparator::expand()
{
  if (!_curr->ready) {
    _curr->ready = true;
  }
}

bool OrderingComparator::tryExpandVarCase(ComparisonNode* node)
{
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
  _curr->n->eqBranch = node->eqBranch;
  _curr->n->gtBranch = node->gtBranch;
  _curr->n->incBranch = node->incBranch;
  _curr->ready = true;
  return true;
}

}