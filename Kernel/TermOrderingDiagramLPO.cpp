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

#include "TermOrderingDiagramLPO.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

void TermOrderingDiagramLPO::processTermNode()
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

    Recycled<DArray<std::pair<Branch,Branch>>> sideBranches;
    sideBranches->init(s->arity());
    (*sideBranches)[0] = { gtBranch, ngeBranch };

    for (unsigned i = 1; i < s->arity(); i++) {
      auto& [majo, alpha] = (*sideBranches)[i];
      auto arg_i = s->arity()-i;

      majo = Branch(lhs,*t->nthArgument(arg_i));
      majo.node()->gtBranch   = (*sideBranches)[i-1].first;
      majo.node()->eqBranch   = ngeBranch;
      majo.node()->ngeBranch  = ngeBranch;

      alpha = Branch(*s->nthArgument(arg_i),rhs);
      alpha.node()->gtBranch  = gtBranch;
      alpha.node()->eqBranch  = gtBranch;
      alpha.node()->ngeBranch = (*sideBranches)[i-1].second;
    }

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
      curr->node()->gtBranch = sideBranches[s->arity()-i-1].first;
      curr->node()->ngeBranch = sideBranches[s->arity()-i-1].second;
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
    auto curr = &_curr->node()->gtBranch;
    for (unsigned i = 1; i < t->arity(); i++) {
      *curr = Branch(lhs,*t->nthArgument(i));
      curr->node()->eqBranch = ngeBranch;
      curr->node()->ngeBranch = ngeBranch;
      curr = &curr->node()->gtBranch;
    }
    *curr = gtBranch;
    break;
  }
  case Ordering::LESS: {
    ASS(s->arity());
    // we mutate the original node in the first iteration
    _curr->node()->lhs = *s->nthArgument(0);
    _curr->node()->rhs = rhs;
    _curr->node()->eqBranch = gtBranch;
    _curr->node()->gtBranch = gtBranch;
    auto curr = &_curr->node()->ngeBranch;
    for (unsigned i = 1; i < s->arity(); i++) {
      *curr = Branch(*s->nthArgument(i),rhs);
      curr->node()->eqBranch = gtBranch;
      curr->node()->gtBranch = gtBranch;
      curr = &curr->node()->ngeBranch;
    }
    *curr = ngeBranch;
    break;
  }
  default:
    ASSERTION_VIOLATION;
  }
}

}
