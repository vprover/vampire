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

bool KBOComparator::check(const SubstApplicator* applicator)
{
  static Stack<TermPairRes> cache;
  cache.reset();
  const auto& kbo = static_cast<const KBO&>(_ord);
  auto curr = &_root;

  while (curr->n) {
    expand(_ord, *curr, cache);
    if (!curr->n) {
      break;
    }
    ASS(curr->n);
    Ordering::Result comp = Ordering::INCOMPARABLE;
    if (curr->tag == BranchTag::T_COMPARISON) {

      auto node = static_cast<ComparisonNode*>(curr->n.ptr());
      comp = kbo.isGreaterOrEq(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
      cache.push({ node->lhs, node->rhs, comp });

    } else {
      ASS(curr->tag == BranchTag::T_WEIGHT);
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

void KBOComparator::expand(const Ordering& ord, Branch& branch, const Stack<TermPairRes>& cache)
{
  const auto& kbo = static_cast<const KBO&>(ord);
  while (branch.tag == BranchTag::T_UNKNOWN)
  {
    // take temporary ownership of node
    Branch nodeHolder = branch;
    auto node = static_cast<ComparisonNode*>(nodeHolder.n.ptr());

    // Use compare here to filter out as many
    // precomputable comparisons as possible.
    auto comp = kbo.compare(node->lhs,node->rhs);
    if (comp != Ordering::INCOMPARABLE) {
      if (comp == Ordering::LESS) {
        branch = node->incBranch;
      } else if (comp == Ordering::GREATER) {
        branch = node->gtBranch;
      } else {
        branch = node->eqBranch;
      }
      continue;
    }
    // If we have a variable, we cannot preprocess further.
    if (node->lhs.isVar() || node->rhs.isVar()) {
      // try cache
      bool found = false;
      for (const auto& [s,t,r] : cache) {
        if (s != node->lhs || t != node->rhs) {
          continue;
        }
        if (r == Ordering::GREATER) {
          branch = node->gtBranch;
        } else if (r == Ordering::EQUAL) {
          branch = node->eqBranch;
        } else {
          ASS_NEQ(r, Ordering::LESS);
          branch = node->incBranch;
        }
        found = true;
        break;
      }
      if (found) {
        continue;
      }
      // make a fresh copy
      branch = Branch(node->lhs, node->rhs);
      // TODO we should replace the node here with a fresh one
      // TODO check node's refcount?
      branch.tag = BranchTag::T_COMPARISON;
      branch.n->eqBranch = node->eqBranch;
      branch.n->gtBranch = node->gtBranch;
      branch.n->incBranch = node->incBranch;
      continue;
    }

    // if both are proper terms, we calculate
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

    auto curr = &branch;

    // if the condition below does not hold, the weight/var balances are satisfied
    if (w < 0 || varInbalance) {
      sort(nonzeros.begin(),nonzeros.end(),[](const auto& e1, const auto& e2) {
        return e1.second>e2.second;
      });
      *curr = Branch(w, std::move(nonzeros));
      curr->n->gtBranch = node->gtBranch;
      curr->n->incBranch = node->incBranch;
      curr = &branch.n->eqBranch;
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

}
