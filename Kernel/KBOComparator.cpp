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
  ScopedPtr nonzeros(new Stack<VarCoeffPair>());
  while (vit.hasNext()) {
    unsigned v;
    int cnt;
    vit.next(v,cnt);
    if (cnt!=0) {
      nonzeros->push(make_pair(v,cnt));
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

  ASS(_curr->node()->lhs.isTerm() && _curr->node()->rhs.isTerm());
  auto lhs = _curr->node()->lhs.term();
  auto rhs = _curr->node()->rhs.term();
  auto eqBranch = _curr->node()->eqBranch;
  auto gtBranch = _curr->node()->gtBranch;
  auto incBranch = _curr->node()->incBranch;

  auto curr = _curr;

  // if the condition below does not hold, the weight/var balances are satisfied
  if (w < 0 || varInbalance) {
    sort(nonzeros->begin(),nonzeros->end(),[](const auto& e1, const auto& e2) {
      return e1.second>e2.second;
    });
    curr->node()->tag = T_WEIGHT;
    curr->node()->w = w;
    curr->node()->varCoeffPairs = nonzeros.release();
    curr->node()->gtBranch = gtBranch;
    curr->node()->incBranch = incBranch;
    curr = &curr->node()->eqBranch;
  }

  Ordering::Result prec = lhs->isSort()
    ? kbo.compareTypeConPrecedences(lhs->functor(),rhs->functor())
    : kbo.compareFunctionPrecedences(lhs->functor(),rhs->functor());
  switch (prec)
  {
    case Ordering::LESS: {
      *curr = incBranch;
      break;
    }
    case Ordering::GREATER: {
      *curr = gtBranch;
      break;
    }
    case Ordering::EQUAL: {
      // push the arguments in reverse order to maintain
      // left-to-right lexicographic order in todo
      for (unsigned i = 0; i < lhs->arity(); i++) {
        auto lhsArg = *lhs->nthArgument(i);
        auto rhsArg = *rhs->nthArgument(i);
        if (!(w < 0 || varInbalance) && i==0) {
          curr->node()->lhs = lhsArg;
          curr->node()->rhs = rhsArg;
        } else {
          *curr = Branch(lhsArg,rhsArg);
          curr->node()->gtBranch = gtBranch;
          curr->node()->incBranch = incBranch;
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
