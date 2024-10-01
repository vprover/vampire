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
    branch->node()->incBranch = fail;
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
    branch = &branch->node()->incBranch;
  }
  *branch = std::move(fail);
}

void LPOComparator::expandTermCase()
{
  // take temporary ownership of node
  auto node = _curr->node();
  auto lhs = node->lhs;
  auto rhs = node->rhs;
  auto eqBranch = node->eqBranch;
  auto gtBranch = node->gtBranch;
  auto incBranch = node->incBranch;

  ASS_EQ(node->tag, T_COMPARISON);
  ASS(!node->ready);
  ASS(lhs.isTerm() && rhs.isTerm());

  const auto& lpo = static_cast<const LPO&>(_ord);
  auto s = lhs.term();
  auto t = rhs.term();

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
        ASS_EQ(curr->node()->tag, T_COMPARISON);
        curr->node()->lhs = s_arg;
        curr->node()->rhs = t_arg;
      } else {
        *curr = Branch(s_arg,t_arg);
      }
      // greater branch is a majo chain
      majoChain(&curr->node()->gtBranch, lhs, rhs.term(), i+1, gtBranch, incBranch);
      // incomparable branch is an alpha chain
      alphaChain(&curr->node()->incBranch, lhs.term(), i+1, rhs, gtBranch, incBranch);
      curr = &curr->node()->eqBranch;
    }
    *curr = eqBranch;
    break;
  }
  case Ordering::GREATER: {
    ASS(t->arity());
    _curr->node()->lhs = lhs;
    _curr->node()->rhs = *t->nthArgument(0);
    _curr->node()->eqBranch = incBranch;
    _curr->node()->incBranch = incBranch;
    majoChain(&_curr->node()->gtBranch, lhs, t, 1, gtBranch, incBranch);
    break;
  }
  case Ordering::LESS: {
    ASS(s->arity());
    _curr->node()->lhs = *s->nthArgument(0);
    _curr->node()->rhs = rhs;
    _curr->node()->eqBranch = gtBranch;
    _curr->node()->gtBranch = gtBranch;
    alphaChain(&_curr->node()->incBranch, s, 1, rhs, gtBranch, incBranch);
    ASS(_curr->node());
    break;
  }
  default:
    ASSERTION_VIOLATION;
  }
}

}
