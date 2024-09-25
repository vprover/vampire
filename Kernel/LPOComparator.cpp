/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "LPO.hpp"

#include "LPOComparator.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

/**
 * Implements an @b LPO::majo call via instructions.
 */
void LPOComparator::majoChain(Branch* branch, TermList tl1, Term* t, unsigned i, Branch success, Branch fail)
{
  ASS(branch);
  for (unsigned j = i; j < t->arity(); j++) {
    *branch = Branch(tl1,*t->nthArgument(j));
    branch->n->eqBranch = fail;
    branch->n->incBranch = fail;
    branch = &branch->n->gtBranch;
  }
  *branch = success;
}

/**
 * Implements an @b LPO::alpha call via instructions.
 */
void LPOComparator::alphaChain(Branch* branch, Term* s, unsigned i, TermList tl2, Branch success, Branch fail)
{
  ASS(branch);
  for (unsigned j = i; j < s->arity(); j++) {
    *branch = Branch(*s->nthArgument(j),tl2);
    branch->n->eqBranch = success;
    branch->n->gtBranch = success;
    branch = &branch->n->incBranch;
  }
  *branch = fail;
}

void LPOComparator::expandTermCase(ComparisonNode* node)
{
  ASS(node->lhs.isTerm() && node->rhs.isTerm());
  const auto& lpo = static_cast<const LPO&>(_ord);
  auto s = node->lhs.term();
  auto t = node->rhs.term();

  switch (lpo.comparePrecedences(s, t)) {
  case Ordering::EQUAL: {
    ASS(s->arity()); // constants cannot be incomparable

    // copies for unification
    auto lhs = node->lhs;
    auto rhs = node->rhs;

    auto curr = _curr;

    // lexicographic comparisons
    for (unsigned i = 0; i < s->arity(); i++)
    {
      auto s_arg = *lhs.term()->nthArgument(i);
      auto t_arg = *rhs.term()->nthArgument(i);
      *curr = Branch(s_arg,t_arg);
      // greater branch is a majo chain
      majoChain(&curr->n->gtBranch, lhs, rhs.term(), i+1, node->gtBranch, node->incBranch);
      // incomparable branch is an alpha chain
      alphaChain(&curr->n->incBranch, lhs.term(), i+1, rhs, node->gtBranch, node->incBranch);
      curr = &curr->n->eqBranch;
    }
    *curr = node->eqBranch;
    break;
  }
  case Ordering::GREATER: {
    ASS(t->arity());
    majoChain(_curr, node->lhs, t, 0, node->gtBranch, node->incBranch);
    break;
  }
  case Ordering::LESS: {
    ASS(s->arity());
    alphaChain(_curr, s, 0, node->rhs, node->gtBranch, node->incBranch);
    break;
  }
  default:
    ASSERTION_VIOLATION;
  }
}

}
