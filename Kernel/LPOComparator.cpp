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

namespace Kernel {

using namespace std;
using namespace Lib;
using namespace Shell;

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

using Node = LPOComparator::Node;
using Branch = Node::Branch;
using BranchTag = Node::BranchTag;

ostream& operator<<(ostream& out, const Node& n)
{
  out << "instr " << n.lhs << " " << n.rhs << " " << n.bs[0] << " " << n.bs[1] << " " << n.bs[2];
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
    for (unsigned j = 0; j < 3; j++) {
      if (st[i].bs[j] == prevBranch) {
        st[i].bs[j] = newBranch;
      }
    }
  }
}

void pushNodes(Stack<Node>& st, const Stack<Node>& other, Branch eqBranch, Branch gtBranch, Branch incBranch)
{
  auto startIndex = st.size();
  for (const auto& n : other) {
    st.push(n);
    for (unsigned j = 0; j < 3; j++) {
      updateBranch(st.top().bs[j], eqBranch, gtBranch, incBranch, startIndex);
    }
  }
}

void deleteDuplicates(Stack<Node>& st)
{
  unsigned removedCnt = 0;
  vmap<Node,unsigned> lastPos;
  vvector<unsigned> removedAfter(st.size(),0);
  for (int i = st.size()-1; i >= 0; i--) {
    auto& curr = st[i];
    for (unsigned j = 0; j < 3; j++) {
      if (curr.bs[j].tag == BranchTag::T_JUMP) {
        auto& jpos = curr.bs[j].jump_pos;
        jpos = lastPos[st[jpos]];
      }
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
    for (unsigned j = 0; j < 3; j++) {
      if (curr.bs[j].tag == BranchTag::T_JUMP) {
        auto& jpos = curr.bs[j].jump_pos;
        jpos -= removedAfter[i]-removedAfter[jpos];
        jpos -= i-res.size();
      }
    }
    res.push(curr);
  }
  swap(res,st);
}

pair<Stack<Node>,BranchTag> LPOComparator::createHelper(TermList tl1, TermList tl2, const LPO& lpo)
{
  auto res = make_pair(Stack<Node>(), BranchTag::T_JUMP);

  auto majoChain = [&lpo](TermList tl1, Term* t, unsigned i) {
    Stack<Node> res;
    int prevIndex = -1;
    for (unsigned j = i; j < t->arity(); j++) {
      auto compRes = createHelper(tl1,*t->nthArgument(j),lpo);
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

  auto alphaChain = [&lpo](Term* s, unsigned i, TermList tl2) {
    Stack<Node> res;
    int prevIndex = -1;
    for (unsigned j = i; j < s->arity(); j++) {
      auto compRes = createHelper(*s->nthArgument(j),tl2,lpo);
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
  auto comp = lpo.compare(tl1,tl2);
  ASS(comp != Ordering::LESS_EQ && comp != Ordering::GREATER_EQ);
  if (comp != Ordering::INCOMPARABLE) {
    if (comp == Ordering::LESS) {
      res.second = BranchTag::T_INCOMPARABLE;
    } else if (comp == Ordering::GREATER) {
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

  switch (lpo.comparePrecedences(s, t)) {
    case Ordering::EQUAL: {
      ASS(s->arity()); // constants cannot be incomparable

      Substitution subst;
      int prevStartIndex = -1;
      unsigned prevEndIndex;

      // lexicographic comparisons
      for (unsigned i = 0; i < s->arity(); i++) {
        auto s_arg = SubstHelper::apply(*s->nthArgument(i),subst);
        auto t_arg = SubstHelper::apply(*t->nthArgument(i),subst);
        auto compRes = createHelper(s_arg,t_arg,lpo);
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
    case Ordering::GREATER: {
      auto subres = majoChain(tl1,t,0);
      if (subres.second == BranchTag::T_JUMP) {
        pushNodes(res.first,subres.first, Branch::eq(), Branch::gt(), Branch::inc());
      } else {
        res.second = subres.second;
      }
      break;
    }
    case Ordering::LESS: {
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

LPOComparator* LPOComparator::create(TermList tl1, TermList tl2, const LPO& lpo)
{
  auto res = new LPOComparator(lpo);
  auto kv = createHelper(tl1, tl2, lpo);
  res->_instructions = kv.first;
  res->_res = kv.second;
  return res;
}

bool LPOComparator::operator()(const SubstApplicator* applicator) const
{
  switch (_res) {
    case BranchTag::T_EQUAL:
    case BranchTag::T_INCOMPARABLE:
      return false;
    case BranchTag::T_GREATER:
      return true;
    case BranchTag::T_JUMP:
      // fallthrough
      break;
  }
  // return lpo(AppliedTerm(lhs,applicator,true),AppliedTerm(rhs,applicator,true))==Ordering::GREATER;
  const auto& st = _instructions;
  unsigned index = 0;
  while (true) {
    const auto& curr = st[index];
    auto comp = _lpo.lpo(AppliedTerm(curr.lhs,applicator,true),AppliedTerm(curr.rhs,applicator,true));
    const auto& branch = curr.getBranch(comp);
    switch (branch.tag) {
      case BranchTag::T_EQUAL:
      case BranchTag::T_INCOMPARABLE:
        return false;
      case BranchTag::T_GREATER:
        return true;
      case BranchTag::T_JUMP:
        ASS_L(index,branch.jump_pos);
        index = branch.jump_pos;
        break;
    }
  }
  ASSERTION_VIOLATION;
}

}
