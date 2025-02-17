/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "KBO.hpp"
#include "SubstHelper.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "KBOComparator.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

void KBOComparator::processTermNode()
{
  const auto& kbo = static_cast<const KBO&>(_ord);

  // weight and variable balances first

  static KBO::State state;
  state.reset();

  auto node = _curr->node();
  state.traverse<1>(kbo, node->lhs);
  state.traverse<-1>(kbo, node->rhs);

  auto w = state._weightDiff;

  bool varInbalance = false;
  // we only care about the non-zero weights and counts
  Stack<VarCoeffPair> nonzeros;
  for (unsigned i = 0; i < state._varDiffs.size(); i++) {
    auto cnt = state._varDiffs[i];
    if (cnt!=0) {
      nonzeros.push({ i, cnt });
      w-=cnt; // we have to remove the variable weights from w
    }
    if (cnt<0) {
      varInbalance = true;
    }
  }

  ASS(node->lhs.isTerm() && node->rhs.isTerm());
  auto lhs = node->lhs.term();
  auto rhs = node->rhs.term();

  auto eqBranch = node->eqBranch;
  auto gtBranch = node->gtBranch;
  auto ngeBranch = node->ngeBranch;

  auto curr = _curr;
  bool weightAdded = (w < 0 || varInbalance);
  if (weightAdded) {
    // we mutate the original node
    curr->node()->tag = Node::T_POLY;
    curr->node()->poly = LinearExpression::get(w, nonzeros);
    curr->node()->gtBranch = gtBranch;
    curr->node()->ngeBranch = ngeBranch;
    curr = &curr->node()->eqBranch;
  }

  Ordering::Result prec = lhs->isSort()
    ? kbo.compareTypeConPrecedences(lhs->functor(),rhs->functor())
    : kbo.compareFunctionPrecedences(lhs->functor(),rhs->functor());
  switch (prec)
  {
    case Ordering::LESS: {
      *curr = ngeBranch;
      break;
    }
    case Ordering::GREATER: {
      *curr = gtBranch;
      break;
    }
    case Ordering::EQUAL: {
      for (unsigned i = 0; i < lhs->arity(); i++) {
        auto lhsArg = *lhs->nthArgument(i);
        auto rhsArg = *rhs->nthArgument(i);
        // we mutate the original node in the first iteration
        if (!weightAdded && i==0) {
          curr->node()->lhs = lhsArg;
          curr->node()->rhs = rhsArg;
        } else {
          *curr = Branch(lhsArg,rhsArg);
          curr->node()->gtBranch = gtBranch;
          curr->node()->ngeBranch = ngeBranch;
        }
        curr = &curr->node()->eqBranch;
      }
      *curr = eqBranch;
      break;
    }
    default: {
      ASSERTION_VIOLATION;
    }
  }
}

}
