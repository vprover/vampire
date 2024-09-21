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

void OrderingComparator::merge(const OrderingComparator& other)
{
  static unsigned ts = 0;
  ts++;

  Stack<std::pair<Branch*,Branch>> todo;
  todo.push(std::make_pair(&_root, other._root));
  while (todo.isNonEmpty()) {
    auto [currB, otherB] = todo.pop();
    // if this branch is successful, or other
    // branch is unsuccessful, we do nothing
    if (currB->tag == BranchTag::T_GREATER
      || otherB.tag == BranchTag::T_NOT_GREATER)
    {
      continue;
    }
    // if this branch is unsuccessful, or other branch
    // is successful, we just replace current with other
    if (currB->tag == BranchTag::T_NOT_GREATER
      || otherB.tag == BranchTag::T_GREATER)
    {
      *currB = otherB;
      continue;
    }
    ASS(currB->n);
    ASS(otherB.n);
    // if we already checked this branch, continue
    if (currB->n->getTs()==ts) {
      continue;
    }
    currB->n->setTs(ts);
    // TODO no node from other should be T_COMPARISON here
    if (currB->tag != otherB.tag || currB->tag != BranchTag::T_COMPARISON) {
      todo.push(std::make_pair(&currB->n->eqBranch, otherB));
      todo.push(std::make_pair(&currB->n->gtBranch, otherB));
      todo.push(std::make_pair(&currB->n->incBranch, otherB));
      continue;
    }
    auto n = static_cast<ComparisonNode*>(currB->n.ptr());
    auto o = static_cast<ComparisonNode*>(otherB.n.ptr());
    if (n->lhs == o->lhs && n->rhs == o->rhs) {
      todo.push(std::make_pair(&currB->n->eqBranch, otherB.n->eqBranch));
      todo.push(std::make_pair(&currB->n->gtBranch, otherB.n->gtBranch));
      todo.push(std::make_pair(&currB->n->incBranch, otherB.n->incBranch));
      continue;
    }
    todo.push(std::make_pair(&currB->n->eqBranch, otherB));
    todo.push(std::make_pair(&currB->n->gtBranch, otherB));
    todo.push(std::make_pair(&currB->n->incBranch, otherB));
  }
}

}