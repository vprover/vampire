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

#include "RobSubstitution.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

bool unify(TermList tl1, TermList tl2, TermList& orig1, TermList& orig2)
{
  RobSubstitution rsubst;
  if (!rsubst.unify(tl1, 0, tl2, 0)) {
    return false;
  }
  Substitution temp;
  VariableIterator vit1(orig1);
  while (vit1.hasNext()) {
    auto v = vit1.next();
    auto vS = rsubst.apply(v,0);
    TermList t;
    if (vS.isVar() && !temp.findBinding(vS.var(), t)) {
      temp.bind(vS.var(), v);
    }
  }
  VariableIterator vit2(orig2);
  while (vit2.hasNext()) {
    auto v = vit2.next();
    auto vS = rsubst.apply(v,0);
    TermList t;
    if (vS.isVar() && !temp.findBinding(vS.var(), t)) {
      temp.bind(vS.var(), v);
    }
  }
  orig1 = SubstHelper::apply(rsubst.apply(orig1,0), temp);
  orig2 = SubstHelper::apply(rsubst.apply(orig2,0), temp);
  return true;
}

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

void LPOComparator::expand(const Ordering& ord, Branch& branch, const Stack<TermPairRes>& cache)
{
  const auto& lpo = static_cast<const LPO&>(ord);
  while (branch.tag == BranchTag::T_UNKNOWN)
  {
    // take temporary ownership of node
    Branch nodeHolder = branch;
    auto node = static_cast<ComparisonNode*>(nodeHolder.n.ptr());
    ASS(node);

    // Use compare here to filter out as many
    // precomputable comparisons as possible.
    auto comp = lpo.compare(node->lhs,node->rhs);
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

    {
      auto s = node->lhs.term();
      auto t = node->rhs.term();

      switch (lpo.comparePrecedences(s, t)) {
      case Ordering::EQUAL: {
        ASS(s->arity()); // constants cannot be incomparable

        // copies for unification
        auto lhs = node->lhs;
        auto rhs = node->rhs;

        auto curr = &branch;

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
          if (!unify(s_arg,t_arg,lhs,rhs)) {
            *curr = node->incBranch;
            goto loop_end;
          }
        }
        *curr = node->eqBranch;
        break;
      }
      case Ordering::GREATER: {
        ASS(t->arity());
        majoChain(&branch, node->lhs, t, 0, node->gtBranch, node->incBranch);
        break;
      }
      case Ordering::LESS: {
        ASS(s->arity());
        alphaChain(&branch, s, 0, node->rhs, node->gtBranch, node->incBranch);
        break;
      }
      default:
        ASSERTION_VIOLATION;
      }
    }
loop_end:
    continue;
  }
}

bool LPOComparator::check(const SubstApplicator* applicator)
{
  static Stack<TermPairRes> cache;
  cache.reset();
  const auto& lpo = static_cast<const LPO&>(_ord);
  auto curr = &_root;

  while (curr->n) {
    expand(_ord, *curr, cache);
    if (!curr->n) {
      break;
    }
    ASS(curr->tag==BranchTag::T_COMPARISON);
    ASS(curr->n);
    auto node = static_cast<ComparisonNode*>(curr->n.ptr());

    auto comp = lpo.lpo(AppliedTerm(node->lhs,applicator,true),AppliedTerm(node->rhs,applicator,true));
    cache.push({ node->lhs, node->rhs, comp });
    curr = &curr->n->getBranch(comp);
  }
  return curr->tag == BranchTag::T_GREATER;
}

}
