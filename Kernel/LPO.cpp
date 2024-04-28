/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file LPO.cpp
 * Implements class LPO for instances of the lexicographic path
 * ordering based on Bernd Loechner's thesis "Advances in
 * Equational Theorem Proving - Architecture, Algorithms, and
 * Redundancy Avoidance" Section 4.2
 */



#include "Lib/Environment.hpp"
#include "Lib/Comparison.hpp"

#include "Shell/Options.hpp"

#include "Kernel/EqHelper.hpp"
#include "Kernel/SubstHelper.hpp"

#include "TermIterators.hpp"
#include "Term.hpp"
#include "LPO.hpp"
#include "Signature.hpp"

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

/**
 * Compare arguments of non-equality literals l1 and l2 and return the
 * result of the comparison.
 */
Ordering::Result LPO::comparePredicates(Literal* l1, Literal *l2) const
{
  ASS(l1->shared());
  ASS(l2->shared());
  ASS(!l1->isEquality());
  ASS(!l2->isEquality());

  unsigned p1 = l1->functor();
  unsigned p2 = l2->functor();

  if (p1 == p2) {
    ASS_EQ(l1->isNegative(), l1->isNegative()) // this assertion is meaningless. 
    //maybe:  ASS_EQ(l1->isNegative(), l2->isNegative())

    // compare arguments in lexicographic order
    for (unsigned i = 0; i < l1->arity(); i++) {
      Result res = compare(*l1->nthArgument(i), *l2->nthArgument(i));
      if (res != EQUAL)
        return res;
    }
    return EQUAL;
  }

  ASS_NEQ(predicatePrecedence(p1), predicatePrecedence(p2)); // precedence should be total
  return (predicatePrecedence(p1) > predicatePrecedence(p2)) ? GREATER : LESS;
} // LPO::comparePredicates()

Ordering::Result LPO::comparePrecedences(const Term* t1, const Term* t2) const
{
  if (t1->isSort() && t2->isSort()) {
    return compareTypeConPrecedences(t1->functor(), t2->functor());
  }
  // type constuctor symbols are less than function symbols
  if (t1->isSort()) {
    return LESS;
  }
  if (t2->isSort()) {
    return GREATER;
  }
  return compareFunctionPrecedences(t1->functor(), t2->functor());
} // LPO::comparePrecedences

Ordering::Result LPO::compare(TermList tl1, TermList tl2) const
{
  return compare(AppliedTerm(tl1),AppliedTerm(tl2));
}

Ordering::Result LPO::compare(AppliedTerm tl1, AppliedTerm tl2) const
{
  if(tl1.equalsShallow(tl2)) {
    return EQUAL;
  }
  if(tl1.term.isVar()) {
    return containsVar(tl2, tl1.term) ? LESS : INCOMPARABLE;
  }
  ASS(tl1.term.isTerm());
  return clpo(tl1, tl2);
}

bool LPO::isGreater(AppliedTerm lhs, AppliedTerm rhs) const
{
  return lpo(lhs,rhs)==GREATER;
}

Ordering::Result LPO::clpo(AppliedTerm tl1, AppliedTerm tl2) const
{
  ASS(tl1.term.isTerm());
  if(tl2.term.isVar()) {
    return containsVar(tl1, tl2.term) ? GREATER : INCOMPARABLE;
  }
  ASS(tl2.term.isTerm());
  auto t1=tl1.term.term();
  auto t2=tl2.term.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return cLMA(tl1, tl2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return cMA(tl1, tl2, t2->args(), t2->arity());
  case LESS:
    return Ordering::reverse(cMA(tl2, tl1, t1->args(), t1->arity()));
  default:
    ASSERTION_VIOLATION;
    // shouldn't happen because symbol precedence is assumed to be
    // total, but if it is not then the following call is correct
    //
    // return cAA(t1, t2, t1->args(), t2->args(), t1->arity(), t2->arity());
  }
}

/*
 * All TermList* are stored in reverse order (by design in Term),
 * hence the weird pointer arithmetic
 */
Ordering::Result LPO::cMA(AppliedTerm s, AppliedTerm t, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    switch(clpo(s, AppliedTerm(*(tl - i),t))) {
    case EQUAL:
    case LESS:
      return LESS;
    case INCOMPARABLE:
      return reverse(alpha(tl - i - 1, arity - i - 1, t, s));
    case GREATER:
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return GREATER;
}

Ordering::Result LPO::cLMA(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    switch(compare(AppliedTerm(*(sl - i),s), AppliedTerm(*(tl - i),t))) {
    case EQUAL:
      break;
    case GREATER:
      return cMA(s, t, tl - i - 1, arity - i - 1);
    case LESS:
      return reverse(cMA(t, s, sl - i - 1, arity - i - 1));
    case INCOMPARABLE:
      return cAA(s, t, sl - i - 1, tl - i - 1, arity - i - 1, arity - i - 1);
    default:
      ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

Ordering::Result LPO::cAA(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity1, unsigned arity2) const
{
  switch (alpha(sl, arity1, s, t)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return reverse(alpha(tl, arity2, t, s));
  default:
    ASSERTION_VIOLATION;
  }
}

// greater iff some exists s_i in sl such that s_i >= t
Ordering::Result LPO::alpha(const TermList* sl, unsigned arity, AppliedTerm s, AppliedTerm t) const
{
  ASS(t.term.isTerm());
  for (unsigned i = 0; i < arity; i++) {
    if (lpo(AppliedTerm(*(sl - i),s), t) != INCOMPARABLE) {
      return GREATER;
    }
  }
  return INCOMPARABLE;
}

// unidirectional comparison function (returns correct result if tt1 > tt2 or tt1 = tt2)
Ordering::Result LPO::lpo(AppliedTerm tt1, AppliedTerm tt2) const
{
  if(tt1.equalsShallow(tt2)) {
    return EQUAL;
  }
  if (tt1.term.isVar()) {
    return (tt1.term==tt2.term) ? EQUAL : INCOMPARABLE;
  }

  if (tt2.term.isVar()) {
    return containsVar(tt1, tt2.term) ? GREATER : INCOMPARABLE;
  }

  auto t1=tt1.term.term();
  auto t2=tt2.term.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return lexMAE(tt1, tt2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return majo(tt1, tt2, t2->args(), t2->arity());
  default:
    return alpha(t1->args(), t1->arity(), tt1, tt2);
  }
}

Ordering::Result LPO::lexMAE(AppliedTerm s, AppliedTerm t, const TermList* sl, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    switch (lpo(AppliedTerm(*(sl - i),s), AppliedTerm(*(tl - i),t))) {
    case EQUAL:
      break;
    case GREATER:
      return majo(s, t, tl - i - 1, arity - i - 1);
    case INCOMPARABLE:
      return alpha(sl - i - 1, arity - i - 1, s, t);
    default:
      ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

// greater if s is greater than every term in tl
Ordering::Result LPO::majo(AppliedTerm s, AppliedTerm t, const TermList* tl, unsigned arity) const
{
  for (unsigned i = 0; i < arity; i++) {
    if (lpo(s, AppliedTerm(*(tl - i), t)) != GREATER) {
      return INCOMPARABLE;
    }
  }
  return GREATER;
}

bool unify(TermList tl1, TermList tl2, Substitution& subst)
{
  Stack<pair<TermList,TermList>> todo;
  todo.push({ tl1,tl2 });
  while (todo.isNonEmpty()) {
    auto [ss,tt] = todo.pop();
    if (ss==tt) {
      continue;
    }
    if (ss.isVar() || tt.isVar()) {
      if (!ss.isVar()) {
        swap(ss,tt);
      }
      if (tt.containsSubterm(ss)) {
        return false;
      }
      subst.bind(ss.var(),tt);
      for (auto& [t1,t2] : todo) {
        t1 = SubstHelper::apply(t1,subst);
        t2 = SubstHelper::apply(t2,subst);
      }
      continue;
    }
    auto s = ss.term();
    auto t = tt.term();
    if (s->functor()!=t->functor()) {
      return false;
    }
    for (unsigned i = 0; i < s->arity(); i++) {
      todo.push({ *s->nthArgument(i), *t->nthArgument(i) });
    }
  }
  return true;
}

using Node = LPO::Node;
using Branch = Node::Branch;
using BranchTag = Node::BranchTag;
using namespace std;

ostream& operator<<(ostream& out, const Node& n)
{
  out << "instr " << n.lhs << " " << n.rhs << " " << n.eqBranch << " " << n.gtBranch << " " << n.incBranch;
  return out;
}

ostream& operator<<(ostream& out, const Branch& b)
{
  if (b.tag == BranchTag::T_JUMP) {
    out << b.jump_pos;
  } else {
    out << b.tag;
  }
  return out;
}

ostream& operator<<(ostream& out, const BranchTag& bt)
{
  switch (bt) {
    case BranchTag::T_EQUAL:
      out << "=";
      break;
    case BranchTag::T_GREATER:
      out << ">";
      break;
    case BranchTag::T_INCOMPARABLE:
      out << "?";
      break;
    case BranchTag::T_JUMP:
      out << "J";
  }
  return out;
}

void outputComparison(const pair<Stack<Node>,BranchTag>& ptr)
{
  switch (ptr.second) {
    case BranchTag::T_EQUAL:
      cout << "equal" << endl;
      return;
    case BranchTag::T_GREATER:
      cout << "greater" << endl;
      return;
    case BranchTag::T_INCOMPARABLE:
      cout << "incomparable" << endl;
      return;
    case BranchTag::T_JUMP:
      // fallthrough
      break;
  }
  for (unsigned i = 0; i < ptr.first.size(); i++) {
    cout << i << " " << ptr.first[i] << endl;
  }
}

void updateBranch(Branch& branch, Branch eqBranch, Branch gtBranch, Branch incBranch, unsigned jump_offset)
{
  switch (branch.tag) {
    case BranchTag::T_EQUAL:
      branch = eqBranch;
      break;
    case BranchTag::T_GREATER:
      branch = gtBranch;
      break;
    case BranchTag::T_INCOMPARABLE:
      branch = incBranch;
      break;
    case BranchTag::T_JUMP:
      branch.jump_pos += jump_offset;
      break;
  }
}

void updateBranchInRange(Stack<Node>& st, unsigned startIndex, unsigned endIndex, Branch prevBranch, Branch newBranch)
{
  for (unsigned i = startIndex; i < endIndex; i++) {
    if (st[i].eqBranch == prevBranch) {
      st[i].eqBranch = newBranch;
    }
    if (st[i].gtBranch == prevBranch) {
      st[i].gtBranch = newBranch;
    }
    if (st[i].incBranch == prevBranch) {
      st[i].incBranch = newBranch;
    }
  }
}

void pushNodes(Stack<Node>& st, const Stack<Node>& other, Branch eqBranch, Branch gtBranch, Branch incBranch)
{
  auto startIndex = st.size();
  for (const auto& n : other) {
    st.push(n);
    updateBranch(st.top().eqBranch, eqBranch, gtBranch, incBranch, startIndex);
    updateBranch(st.top().gtBranch, eqBranch, gtBranch, incBranch, startIndex);
    updateBranch(st.top().incBranch, eqBranch, gtBranch, incBranch, startIndex);
  }
}

void deleteDuplicates(Stack<Node>& st)
{
  unsigned removedCnt = 0;
  vmap<Node,unsigned> lastPos;
  vvector<unsigned> removedAfter(st.size(),0);
  for (int i = st.size()-1; i >= 0; i--) {
    auto& curr = st[i];
    if (curr.eqBranch.tag == BranchTag::T_JUMP) {
      auto& jpos = curr.eqBranch.jump_pos;
      jpos = lastPos[st[jpos]];
    }
    if (curr.gtBranch.tag == BranchTag::T_JUMP) {
      auto& jpos = curr.gtBranch.jump_pos;
      jpos = lastPos[st[jpos]];
    }
    if (curr.incBranch.tag == BranchTag::T_JUMP) {
      auto& jpos = curr.incBranch.jump_pos;
      jpos = lastPos[st[jpos]];
    }

    if (lastPos.insert({ curr, i }).second) {
      removedAfter[i] = removedCnt;
    } else {
      removedCnt++;
    }
  }
  ASS_EQ(lastPos[st[0]],0);
  if (!removedCnt) {
    return;
  }

  Stack<Node> res;
  for (unsigned i = 0; i < st.size(); i++) {
    auto curr = st[i];
    if (lastPos[curr]!=i) {
      continue;
    }
    if (curr.eqBranch.tag == BranchTag::T_JUMP) {
      auto& jpos = curr.eqBranch.jump_pos;
      jpos -= removedAfter[i]-removedAfter[jpos];
      jpos -= i-res.size();
    }
    if (curr.gtBranch.tag == BranchTag::T_JUMP) {
      auto& jpos = curr.gtBranch.jump_pos;
      jpos -= removedAfter[i]-removedAfter[jpos];
      jpos -= i-res.size();
    }
    if (curr.incBranch.tag == BranchTag::T_JUMP) {
      auto& jpos = curr.incBranch.jump_pos;
      jpos -= removedAfter[i]-removedAfter[jpos];
      jpos -= i-res.size();
    }
    res.push(curr);
  }
  swap(res,st);
}

pair<Stack<Node>,BranchTag> LPO::preprocessComparison(TermList tl1, TermList tl2) const
{
  auto res = make_pair(Stack<Node>(), BranchTag::T_JUMP);

  auto majoChain = [this](TermList tl1, Term* t, unsigned i) {
    Stack<Node> res;
    int prevIndex = -1;
    for (unsigned j = i; j < t->arity(); j++) {
      auto compRes = preprocessComparison(tl1,*t->nthArgument(j));
      if (compRes.second == BranchTag::T_GREATER) {
        continue;
      }
      if (compRes.second != BranchTag::T_JUMP) {
        res.reset();
        return make_pair(res,BranchTag::T_INCOMPARABLE);
      }
      if (prevIndex != -1) {
        updateBranchInRange(res, prevIndex, (unsigned)res.size(),
          Branch::gt(), Branch::jump(res.size()));
      }
      prevIndex = res.size();
      pushNodes(res,compRes.first, Branch::inc(), Branch::gt(), Branch::inc());
    }
    return make_pair(res,res.isEmpty() ? BranchTag::T_GREATER : BranchTag::T_JUMP);
  };

  auto alphaChain = [this](Term* s, unsigned i, TermList tl2) {
    Stack<Node> res;
    int prevIndex = -1;
    for (unsigned j = i; j < s->arity(); j++) {
      auto compRes = preprocessComparison(*s->nthArgument(j),tl2);
      if (compRes.second == BranchTag::T_INCOMPARABLE) {
        continue;
      }
      if (compRes.second != BranchTag::T_JUMP) {
        res.reset();
        return make_pair(res,BranchTag::T_GREATER);
      }
      if (prevIndex != -1) {
        updateBranchInRange(res, prevIndex, (unsigned)res.size(),
          Branch::inc(), Branch::jump(res.size()));
      }
      prevIndex = res.size();
      pushNodes(res,compRes.first, Branch::gt(), Branch::gt(), Branch::inc());
    }
    return make_pair(res,res.isEmpty() ? BranchTag::T_INCOMPARABLE : BranchTag::T_JUMP);
  };

  // use compare here to filter out as many
  // precomputable comparisons as possible
  auto comp = compare(tl1,tl2);
  ASS(comp != LESS_EQ && comp != GREATER_EQ);
  if (comp != INCOMPARABLE) {
    if (comp == LESS) {
      res.second = BranchTag::T_INCOMPARABLE;
    } else if (comp == GREATER) {
      res.second = BranchTag::T_GREATER;
    } else {
      res.second = BranchTag::T_EQUAL;
    }
    return res;
  }
  if (tl1.isVar() || tl2.isVar()) {
    res.first.push(Node(tl1,tl2));
    return res;
  }

  auto s = tl1.term();
  auto t = tl2.term();

  switch (comparePrecedences(s, t)) {
    case EQUAL: {
      ASS(s->arity()); // constants cannot be incomparable

      Substitution subst;
      int prevStartIndex = -1;
      unsigned prevEndIndex;

      // lexicographic comparisons
      for (unsigned i = 0; i < s->arity(); i++) {
        auto s_arg = SubstHelper::apply(*s->nthArgument(i),subst);
        auto t_arg = SubstHelper::apply(*t->nthArgument(i),subst);
        auto compRes = preprocessComparison(s_arg,t_arg);
        if (compRes.second == BranchTag::T_EQUAL) {
          ALWAYS(unify(s_arg,t_arg,subst));
          continue;
        }

        auto majoRes = majoChain(SubstHelper::apply(tl1,subst),SubstHelper::apply(tl2,subst).term(),i+1);
        if (compRes.second == BranchTag::T_GREATER) {
          // finish with majo branch
          if (majoRes.second != BranchTag::T_JUMP) {
            if (prevStartIndex != 1) {
              updateBranchInRange(res.first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch{ majoRes.second, 0 });
            } else {
              res.first.reset();
              res.second = majoRes.second;
            }
          } else {
            if (prevStartIndex != -1) {
              updateBranchInRange(res.first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch::jump(res.first.size()));
            }
            pushNodes(res.first,majoRes.first, Branch::eq(), Branch::gt(), Branch::inc());
          }
          break;
        }

        auto alphaRes = alphaChain(SubstHelper::apply(tl1,subst).term(),i+1,SubstHelper::apply(tl2,subst));
        if (compRes.second == BranchTag::T_INCOMPARABLE) {
          // finish with alpha branch
          if (alphaRes.second != BranchTag::T_JUMP) {
            if (prevStartIndex != 1) {
              updateBranchInRange(res.first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch{ alphaRes.second, 0 });
            } else {
              res.first.reset();
              res.second = alphaRes.second;
            }
          } else {
            if (prevStartIndex != -1) {
              updateBranchInRange(res.first, prevStartIndex, prevEndIndex,
                Branch::eq(), Branch::jump(res.first.size()));
            }
            pushNodes(res.first,alphaRes.first, Branch::eq(), Branch::gt(), Branch::inc());
          }
          break;
        }

        if (prevStartIndex != 1) {
          updateBranchInRange(res.first, prevStartIndex, prevEndIndex,
            Branch::eq(), Branch::jump(res.first.size()));
        }
        prevStartIndex = res.first.size();
        prevEndIndex = res.first.size() + compRes.first.size();
        Branch majoBranch{
          majoRes.second,
          (uint16_t)(majoRes.second == BranchTag::T_JUMP ? res.first.size() + compRes.first.size() : 0)
        };
        Branch alphaBranch{
          alphaRes.second,
          (uint16_t)(alphaRes.second == BranchTag::T_JUMP ? res.first.size() + compRes.first.size() + majoRes.first.size() : 0)
        };

        pushNodes(res.first, compRes.first, Branch::eq(), majoBranch, alphaBranch);

        if (majoRes.second == BranchTag::T_JUMP) {
          pushNodes(res.first, majoRes.first, Branch::eq(), Branch::gt(), Branch::inc());
        }

        if (alphaRes.second == BranchTag::T_JUMP) {
          pushNodes(res.first, alphaRes.first, Branch::eq(), Branch::gt(), Branch::inc());
        }

        if (!unify(s_arg,t_arg,subst)) {
          updateBranchInRange(res.first, prevStartIndex, prevEndIndex, Branch::eq(), Branch::inc());
          break;
        }
      }
      break;
    }
    case GREATER: {
      auto subres = majoChain(tl1,t,0);
      if (subres.second == BranchTag::T_JUMP) {
        pushNodes(res.first,subres.first, Branch::eq(), Branch::gt(), Branch::inc());
      } else {
        res.second = subres.second;
      }
      break;
    }
    case LESS: {
      auto subres = alphaChain(s,0,tl2);
      if (subres.second == BranchTag::T_JUMP) {
        pushNodes(res.first,subres.first, Branch::eq(), Branch::gt(), Branch::inc());
      } else {
        res.second = subres.second;
      }
      break;
    }
    default:
      ASSERTION_VIOLATION;
  }
  ASS(res.second == BranchTag::T_JUMP || res.first.isEmpty());
  deleteDuplicates(res.first);
  return res;
}

bool LPO::isGreater(TermList lhs, TermList rhs, const SubstApplicator* applicator, Stack<Instruction>*& instructions) const
{
  pair<Stack<Node>,BranchTag>* ptr;
  if (_comparisons.getValuePtr(make_pair(lhs,rhs),ptr)) {
    *ptr = preprocessComparison(lhs,rhs);
    // cout << "preprocessing " << lhs << " " << rhs << endl;
    // outputComparison(*ptr);
    // cout << endl;
  }
  switch (ptr->second) {
    case BranchTag::T_EQUAL:
      return false;
    case BranchTag::T_GREATER:
      return true;
    case BranchTag::T_INCOMPARABLE:
      return false;
    case BranchTag::T_JUMP:
      // fallthrough
      break;
  }
  // return lpo(AppliedTerm(lhs,applicator,true),AppliedTerm(rhs,applicator,true))==GREATER;
  const auto& st = ptr->first;
  unsigned index = 0;
  while (true) {
    const auto& curr = st[index];
    auto comp = lpo(AppliedTerm(curr.lhs,applicator,true),AppliedTerm(curr.rhs,applicator,true));
    const auto& branch = curr.getBranch(comp);
    switch (branch.tag) {
      case BranchTag::T_EQUAL:
        return false;
      case BranchTag::T_GREATER:
        return true;
      case BranchTag::T_INCOMPARABLE:
        return false;
      case BranchTag::T_JUMP:
        ASS_L(index,branch.jump_pos);
        index = branch.jump_pos;
        break;
    }
  }
  ASSERTION_VIOLATION;
}

void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
