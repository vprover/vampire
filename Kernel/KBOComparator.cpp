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

void KBOComparator::expandTermCase()
{
  // take temporary ownership of node
  Branch nodeHolder = *_curr;
  auto node = static_cast<ComparisonNode*>(nodeHolder.n.ptr());

  ASS(node->lhs.isTerm() && node->rhs.isTerm());
  const auto& kbo = static_cast<const KBO&>(_ord);

  // weight and variable balances first

  // we only care about the non-zero weights and counts
  bool varInbalance = false;
  auto state = kbo._state;
#if VDEBUG
  // we make sure kbo._state is not used while we're using it
  kbo._state = nullptr;
#endif
  auto w = state->_weightDiff;
  decltype(state->_varDiffs)::Iterator vit(state->_varDiffs);
  Stack<VarCoeffPair> nonzeros;
  while (vit.hasNext()) {
    unsigned v;
    int cnt;
    vit.next(v,cnt);
    if (cnt!=0) {
      nonzeros.push(make_pair(v,cnt));
      w-=cnt; // we have to remove the variable weights from w
    }
    if (cnt<0) {
      varInbalance = true;
    }
  }
#if VDEBUG
  kbo._state = state;
  state = nullptr;
#endif

  auto curr = _curr;

  // if the condition below does not hold, the weight/var balances are satisfied
  if (w < 0 || varInbalance) {
    sort(nonzeros.begin(),nonzeros.end(),[](const auto& e1, const auto& e2) {
      return e1.second>e2.second;
    });
    *curr = Branch(w, std::move(nonzeros));
    curr->n->gtBranch = node->gtBranch;
    curr->n->incBranch = node->incBranch;
    curr = &curr->n->eqBranch;
  }

  auto lhst = node->lhs.term();
  auto rhst = node->rhs.term();

  Ordering::Result prec = lhst->isSort()
    ? kbo.compareTypeConPrecedences(lhst->functor(),rhst->functor())
    : kbo.compareFunctionPrecedences(lhst->functor(),rhst->functor());
  switch (prec)
  {
    case Ordering::LESS: {
      *curr = node->incBranch;
      break;
    }
    case Ordering::GREATER: {
      *curr = node->gtBranch;
      break;
    }
    case Ordering::EQUAL: {
      // push the arguments in reverse order to maintain
      // left-to-right lexicographic order in todo
      for (unsigned i = 0; i < lhst->arity(); i++) {
        auto lhsArg = *lhst->nthArgument(i);
        auto rhsArg = *rhst->nthArgument(i);
        *curr = Branch(lhsArg,rhsArg);
        curr->n->gtBranch = node->gtBranch;
        curr->n->incBranch = node->incBranch;
        curr = &curr->n->eqBranch;
      }
      *curr = node->eqBranch;
      break;
    }
    default: {
      ASSERTION_VIOLATION;
    }
  }
}

}
