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
    case OrderingComparator::BranchTag::T_NOT_GREATER:
      out << "!>";
      break;
    case OrderingComparator::BranchTag::T_GREATER:
      out << ">";
      break;
    case OrderingComparator::BranchTag::T_COMPARISON:
      out << "$";
      break;
    case OrderingComparator::BranchTag::T_WEIGHT:
      out << "w";
      break;
    case OrderingComparator::BranchTag::T_UNKNOWN:
      out << "?";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator::Branch& branch)
{
  str << branch.tag << " ";
  if (branch.n) {
    if (branch.tag==OrderingComparator::BranchTag::T_WEIGHT) {
      auto n = static_cast<OrderingComparator::WeightNode*>(branch.n.ptr());
      str << n->w << " ";
      for (const auto& [var, coeff] : n->varCoeffPairs) {
        str << "X" << var << " " << coeff << " ";
      }
    } else {
      auto n = static_cast<OrderingComparator::ComparisonNode*>(branch.n.ptr());
      str << n->lhs << " " << n->rhs;
    }
  } else {
    str << "null";
  }
  return str;
}

std::ostream& operator<<(std::ostream& str, const OrderingComparator& comp)
{
  Stack<std::pair<const OrderingComparator::Branch*, unsigned>> todo;
  todo.push(std::make_pair(&comp._root,0));
  unsigned cnt = 1;

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    str << cnt++ << " ";
    for (unsigned i = 0; i < kv.second; i++) {
      str << "  ";
    }
    str << *kv.first << std::endl;
    if (kv.first->n) {
      todo.push(std::make_pair(&kv.first->n->incBranch,kv.second+1));
      todo.push(std::make_pair(&kv.first->n->gtBranch,kv.second+1));
      todo.push(std::make_pair(&kv.first->n->eqBranch,kv.second+1));
    }
  }
  return str;
}

OrderingComparator::~OrderingComparator() = default;

bool OrderingComparator::check(const SubstApplicator* applicator)
{
  static Stack<TermPairRes> cache;
  cache.reset();
  auto curr = &_root;

  while (curr->n) {
    expand(*curr, cache);
    if (!curr->n) {
      break;
    }
    ASS(curr->n);
    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (curr->tag == BranchTag::T_COMPARISON) {

      auto node = static_cast<ComparisonNode*>(curr->n.ptr());
      comp = _ord.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
      cache.push({ node->lhs, node->rhs, comp });

    } else {
      ASS(curr->tag == BranchTag::T_WEIGHT);

      const auto& kbo = static_cast<const KBO&>(_ord);
      auto node = static_cast<WeightNode*>(curr->n.ptr());
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
    curr = &curr->n->getBranch(comp);
  }
  return curr->tag == BranchTag::T_GREATER;
}

void OrderingComparator::merge(const OrderingComparator& other)
{
  ASS(other._root.tag == BranchTag::T_UNKNOWN);

  static unsigned ts = 0;
  ts++;

  Stack<std::pair<Branch*,Branch>> todo;

  auto pushBranches = [&todo](Branch* b, const Branch& other) {
    // if other branch is unsuccessful, do nothing
    if (b->tag == BranchTag::T_GREATER || other.tag == BranchTag::T_NOT_GREATER) {
      return;
    }
    // if this branch is unsuccessful, replace this with other
    if (b->tag == BranchTag::T_NOT_GREATER || other.tag == BranchTag::T_GREATER) {
      *b = other;
      return;
    }
    todo.push(std::make_pair(b,other));
  };

  pushBranches(&_root, other._root);

  while (todo.isNonEmpty()) {
    auto [currB, otherB] = todo.pop();
    ASS(currB->n);
    ASS(otherB.n);
    // if we already checked this branch, continue
    if (currB->n->getTs()==ts) {
      continue;
    }
    currB->n->setTs(ts);
    if (currB->tag == BranchTag::T_UNKNOWN && currB->tag != BranchTag::T_COMPARISON) {
      // both must be comparison nodes
      auto n = static_cast<ComparisonNode*>(currB->n.ptr());
      auto o = static_cast<ComparisonNode*>(otherB.n.ptr());
      if (n->lhs == o->lhs && n->rhs == o->rhs) {
        pushBranches(&currB->n->eqBranch, otherB.n->eqBranch);
        pushBranches(&currB->n->gtBranch, otherB.n->gtBranch);
        pushBranches(&currB->n->incBranch, otherB.n->incBranch);
        continue;
      }
    }
    pushBranches(&currB->n->eqBranch, otherB);
    pushBranches(&currB->n->gtBranch, otherB);
    pushBranches(&currB->n->incBranch, otherB);
  }
}

void OrderingComparator::expand(Branch& branch, const Stack<TermPairRes>& cache)
{
  if (branch.tag == BranchTag::T_UNKNOWN) {
    branch.tag = BranchTag::T_COMPARISON;
  }
}

bool OrderingComparator::tryVarVarCase(Branch& branch, const Stack<TermPairRes>& cache, ComparisonNode* node)
{
  // If we have a variable, we cannot preprocess further.
  if (!node->lhs.isVar() && !node->rhs.isVar()) {
    return false;
  }
  // try cache
  for (const auto& [s,t,r] : cache) {
    if (s == node->lhs && t == node->rhs) {
      if (r == Ordering::GREATER) {
        branch = node->gtBranch;
      } else if (r == Ordering::EQUAL) {
        branch = node->eqBranch;
      } else {
        ASS_EQ(r, Ordering::INCOMPARABLE);
        branch = node->incBranch;
      }
      return true;
    }
    
    if (s == node->rhs && t == node->lhs && r != Ordering::INCOMPARABLE) {
      if (r == Ordering::GREATER) {
        branch = node->incBranch;
      } else {
        ASS_EQ(r, Ordering::EQUAL);
        branch = node->eqBranch;
      }
      // Note: since we use isGreater which results
      // in INCOMPARABLE when compare would be LESS,
      // the INCOMPARABLE result we cannot use here
      return true;
    }
  }
  // make a fresh copy
  branch = Branch(node->lhs, node->rhs);
  branch.tag = BranchTag::T_COMPARISON;
  branch.n->eqBranch = node->eqBranch;
  branch.n->gtBranch = node->gtBranch;
  branch.n->incBranch = node->incBranch;
  return true;
}

}