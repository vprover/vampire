/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

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

LPOComparator::LPOComparator(TermList lhs, TermList rhs, const LPO& lpo)
  : OrderingComparator(lhs, rhs, lpo), _root(lhs, rhs)
{
}

ostream& operator<<(ostream& out, const LPOComparator::BranchTag& t)
{
  switch (t) {
    case LPOComparator::BranchTag::T_NOT_GREATER:
      out << "!>";
      break;
    case LPOComparator::BranchTag::T_GREATER:
      out << ">";
      break;
    case LPOComparator::BranchTag::T_COMPARISON:
      out << "$";
      break;
    case LPOComparator::BranchTag::T_UNKNOWN:
      out << "?";
      break;
  }
  return out;
}

std::ostream& operator<<(std::ostream& str, const LPOComparator::Branch& branch)
{
  str << branch.tag << " ";
  if (branch.n) {
    str << branch.n->lhs << " " << branch.n->rhs;
  } else {
    str << "null";
  }
  return str;
}

ostream& operator<<(ostream& str, const LPOComparator& comp)
{
  str << "comparator for " << comp._lhs << " > " << comp._rhs << endl;
  Stack<pair<const LPOComparator::Branch*, unsigned>> todo;
  todo.push(make_pair(&comp._root,0));
  unsigned cnt = 1;

  while (todo.isNonEmpty()) {
    auto kv = todo.pop();
    str << cnt++ << " ";
    for (unsigned i = 0; i < kv.second; i++) {
      str << "  ";
    }
    str << *kv.first << endl;
    if (kv.first->n) {
      todo.push(make_pair(&kv.first->n->incBranch,kv.second+1));
      todo.push(make_pair(&kv.first->n->gtBranch,kv.second+1));
      todo.push(make_pair(&kv.first->n->eqBranch,kv.second+1));
    }
  }
  return str;
}

std::string LPOComparator::toString() const
{
  std::stringstream str;
  str << *this << endl;
  return str.str();
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

void LPOComparator::expand(Branch& branch, const LPO& lpo)
{
  while (branch.tag == BranchTag::T_UNKNOWN)
  {
    // take temporary ownership of node
    Branch nodeHolder = branch;
    auto node = nodeHolder.n.ptr();

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
      branch.tag = BranchTag::T_COMPARISON;
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
  const auto& lpo = static_cast<const LPO&>(_ord);
  auto curr = &_root;

  while (curr->n) {
    expand(*curr, lpo);
    if (!curr->n) {
      break;
    }
    ASS(curr->n);
    auto comp = lpo.lpo(AppliedTerm(curr->n->lhs,applicator,true),AppliedTerm(curr->n->rhs,applicator,true));
    curr = &curr->n->getBranch(comp);
  }
  return curr->tag == BranchTag::T_GREATER;
}

}
