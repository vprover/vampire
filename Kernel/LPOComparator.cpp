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
    branch->node()->eqBranch = fail;
    branch->node()->ngeBranch = fail;
    branch = &branch->node()->gtBranch;
  }
  *branch = std::move(success);
}

/**
 * Implements an @b LPO::alpha call via instructions.
 */
void LPOComparator::alphaChain(Branch* branch, Term* s, unsigned i, TermList tl2, Branch success, Branch fail)
{
  ASS(branch);
  for (unsigned j = i; j < s->arity(); j++) {
    *branch = Branch(*s->nthArgument(j),tl2);
    branch->node()->eqBranch = success;
    branch->node()->gtBranch = success;
    branch = &branch->node()->ngeBranch;
  }
  *branch = std::move(fail);
}

void LPOComparator::processTermNode()
{
  // take temporary ownership of node
  auto node = _curr->node();
  auto lhs = node->lhs;
  auto rhs = node->rhs;
  auto eqBranch = node->eqBranch;
  auto gtBranch = node->gtBranch;
  auto ngeBranch = node->ngeBranch;

  ASS_EQ(node->tag, Node::T_TERM);
  ASS(!node->ready);

  ASS(lhs.isTerm() && rhs.isTerm());
  auto s = lhs.term();
  auto t = rhs.term();

  const auto& lpo = static_cast<const LPO&>(_ord);
  switch (lpo.comparePrecedences(s, t)) {
  case Ordering::EQUAL: {
    ASS(s->arity()); // constants cannot be incomparable
    auto curr = _curr;

    // lexicographic comparisons
    for (unsigned i = 0; i < s->arity(); i++)
    {
      auto s_arg = *lhs.term()->nthArgument(i);
      auto t_arg = *rhs.term()->nthArgument(i);
      if (i == 0) {
        // we mutate the original node in the first iteration
        ASS_EQ(curr->node()->tag, Node::T_TERM);
        curr->node()->lhs = s_arg;
        curr->node()->rhs = t_arg;
      } else {
        *curr = Branch(s_arg,t_arg);
      }
      // TODO point to the existing chain if there is one
      // greater branch is a majo chain
      majoChain(&curr->node()->gtBranch, lhs, rhs.term(), i+1, gtBranch, ngeBranch);
      // incomparable branch is an alpha chain
      alphaChain(&curr->node()->ngeBranch, lhs.term(), i+1, rhs, gtBranch, ngeBranch);
      curr = &curr->node()->eqBranch;
    }
    *curr = eqBranch;
    break;
  }
  case Ordering::GREATER: {
    ASS(t->arity());
    // we mutate the original node in the first iteration
    _curr->node()->lhs = lhs;
    _curr->node()->rhs = *t->nthArgument(0);
    _curr->node()->eqBranch = ngeBranch;
    _curr->node()->ngeBranch = ngeBranch;
    majoChain(&_curr->node()->gtBranch, lhs, t, 1, gtBranch, ngeBranch);
    break;
  }
  case Ordering::LESS: {
    ASS(s->arity());
    // we mutate the original node in the first iteration
    _curr->node()->lhs = *s->nthArgument(0);
    _curr->node()->rhs = rhs;
    _curr->node()->eqBranch = gtBranch;
    _curr->node()->gtBranch = gtBranch;
    alphaChain(&_curr->node()->ngeBranch, s, 1, rhs, gtBranch, ngeBranch);
    break;
  }
  default:
    ASSERTION_VIOLATION;
  }
}

}
