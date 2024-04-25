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

vstring nodeToString(const Stack<LPO::Node>& st, unsigned i)
{
  switch (st[i].tag) {
    case LPO::Node::Tag::T_CONDITIONAL:
      return "CONDITIONAL";
    case LPO::Node::Tag::T_COMPARISON: {
      auto s = st[i+1].term;
      auto t = st[i+2].term;
      return "COMPARE " + s.toString() + " " + t.toString();
    }
    case LPO::Node::Tag::T_EQUAL:
      return "EQUAL";
    case LPO::Node::Tag::T_GREATER:
      return "GREATER";
    case LPO::Node::Tag::T_INCOMPARABLE:
      return "INCOMPARABLE";
    case LPO::Node::Tag::T_JUMP:
      return "JUMP " + Int::toString(st[i].offset);
    case LPO::Node::Tag::T_TERM:
      return "TERM " + st[i].term.toString();
  }
  ASSERTION_VIOLATION;
}

constexpr unsigned c_offset(LPO::Node::Tag t)
{
  if (t==LPO::Node::Tag::T_EQUAL) {
    return 1;
  } else if (t==LPO::Node::Tag::T_GREATER) {
    return 2;
  } else if (t==LPO::Node::Tag::T_INCOMPARABLE) {
    return 3;
  } else {
    ASSERTION_VIOLATION;
  }
}

void outputNodes(const Stack<LPO::Node>& st)
{
  cout << "size " << st.size() << endl;
  for (unsigned i = 0; i < st.size();) {
    cout << i << " " << nodeToString(st,i) << endl;
    if (st[i].tag==LPO::Node::Tag::T_COMPARISON) {
      i+=3;
    } else {
      i++;
    }
  }
}

Stack<LPO::Node>* LPO::preprocessComparison(TermList tl1, TermList tl2) const
{
  Stack<Node>** ptr;
  if (!_comparisons.getValuePtr(make_pair(tl1,tl2),ptr)) {
    return *ptr;
  }

  auto res = new Stack<Node>();
  *ptr = res;

  using Tag = Node::Tag;

  auto majoChain = [this](TermList tl1, Term* t, unsigned i) {
    Stack<Node> res;
    unsigned lastGtIndex = 0;
    for (unsigned j = i; j < t->arity(); j++) {
      // cout << "majo subcase " << tl1 << " " << *t->nthArgument(j) << endl;
      auto compNode = preprocessComparison(tl1,*t->nthArgument(j));
      // outputNodes(*compNode);
      // cout << endl;
      auto firstTag = (*compNode)[0].tag;
      if (firstTag == Tag::T_GREATER) {
        continue;
      }
      if (firstTag == Tag::T_EQUAL || firstTag == Tag::T_INCOMPARABLE) {
        if (res.isEmpty()) {
          res.push(Node(Tag::T_INCOMPARABLE));
        } else {
          res[lastGtIndex] = Node(Tag::T_INCOMPARABLE);
        }
        return res;
      }
      res.push(Node(Tag::T_CONDITIONAL));
      // eqbranch
      res.push(Node(Tag::T_INCOMPARABLE));
      // gtBranch
      lastGtIndex = res.size();
      res.push(Node(2+compNode->size()));
      // incBranch
      res.push(Node(Tag::T_INCOMPARABLE));
      res.loadFromIterator(Stack<Node>::BottomFirstIterator(*compNode));
    }
    if (res.isEmpty()) {
      res.push(Node(Tag::T_GREATER));
    } else {
      res[lastGtIndex] = Node(Tag::T_GREATER);
    }
    return res;
  };

  auto alphaChain = [this](Term* s, unsigned i, TermList tl2) {
    Stack<Node> res;
    unsigned lastIncIndex = 0;
    for (unsigned j = i; j < s->arity(); j++) {
      auto compNode = preprocessComparison(*s->nthArgument(j),tl2);
      auto firstTag = (*compNode)[0].tag;
      if (firstTag == Tag::T_INCOMPARABLE) {
        continue;
      }
      if (firstTag == Tag::T_EQUAL || firstTag == Tag::T_GREATER) {
        if (res.isEmpty()) {
          res.push(Node(Tag::T_GREATER));
        } else {
          res[lastIncIndex] = Node(Tag::T_GREATER);
        }
        return res;
      }
      res.push(Node(Tag::T_CONDITIONAL));
      // eqBranch
      res.push(Node(Tag::T_GREATER));
      // gtBranch
      res.push(Node(Tag::T_GREATER));
      lastIncIndex = res.size();
      res.push(Node(1+compNode->size())); // incbranch jump offset
      res.loadFromIterator(Stack<Node>::BottomFirstIterator(*compNode));
    }
    if (res.isEmpty()) {
      res.push(Node(Tag::T_INCOMPARABLE));
    } else {
      res[lastIncIndex] = Node(Tag::T_INCOMPARABLE);
    }
    return res;
  };

  // use compare here to filter out as many
  // precomputable comparisons as possible
  auto comp = compare(tl1,tl2);
  ASS(comp != LESS_EQ && comp != GREATER_EQ);
  if (comp != INCOMPARABLE) {
    if (comp == LESS) {
      res->push(Node(Tag::T_INCOMPARABLE));
    } else if (comp == GREATER) {
      res->push(Node(Tag::T_GREATER));
    } else {
      res->push(Node(Tag::T_EQUAL));
    }
    return res;
  }
  if (tl1.isVar() || tl2.isVar()) {
    res->push(Node(Tag::T_COMPARISON));
    res->push(Node(tl1));
    res->push(Node(tl2));
    return res;
  }

  auto s = tl1.term();
  auto t = tl2.term();

  switch (comparePrecedences(s, t)) {
    case EQUAL: {
      ASS(s->arity()); // constants cannot be incomparable

      Substitution subst;
      unsigned lastEqIndex = 0;

      // lexicographic comparisons
      bool canBeEqual = true;
      bool earlyReturn = false;
      for (unsigned i = 0; i < s->arity(); i++) {
        auto s_arg = SubstHelper::apply(*s->nthArgument(i),subst);
        auto t_arg = SubstHelper::apply(*t->nthArgument(i),subst);
        // cout << "lex subcase " << s_arg << " " << t_arg << endl;
        auto compNode = preprocessComparison(s_arg,t_arg);
        // outputNodes(*compNode);
        // cout << endl;
        ASS(compNode->isNonEmpty());
        if ((*compNode)[0].tag == Tag::T_EQUAL) {
          ALWAYS(unify(s_arg,t_arg,subst));
          continue;
        }

        auto majoNode = majoChain(SubstHelper::apply(tl1,subst),SubstHelper::apply(tl2,subst).term(),i+1);
        // if ((*compNode)[0].tag == Tag::GREATER) {
        //   if (prev) {
        //     prev->eqBranch = majoNode;
        //   } else {
        //     res = majoNode;
        //   }
        //   earlyReturn = true;
        //   break;
        // }
        auto alphaNode = alphaChain(SubstHelper::apply(tl1,subst).term(),i+1,SubstHelper::apply(tl2,subst));
        // if (compNode->isResult(INCOMPARABLE)) {
        //   if (prev) {
        //     prev->eqBranch = alphaNode;
        //   } else {
        //     res = alphaNode;
        //   }
        //   earlyReturn = true;
        //   break;
        // }

        res->push(Node(Tag::T_CONDITIONAL));
        // eqBranch
        lastEqIndex = res->size();
        res->push(Node(3+compNode->size()+majoNode.size()+alphaNode.size()));
        // gtBranch
        res->push(Node(2+compNode->size()));
        // incBranch
        res->push(Node(1+compNode->size()+majoNode.size()));
        res->loadFromIterator(Stack<Node>::BottomFirstIterator(*compNode));
        res->loadFromIterator(Stack<Node>::BottomFirstIterator(majoNode));
        res->loadFromIterator(Stack<Node>::BottomFirstIterator(alphaNode));

        if (!unify(s_arg,t_arg,subst)) {
          canBeEqual = false;
          break;
        }
        // outputNodes(*res);
      }
      if (!earlyReturn) {
        // cout << "setting eq branch at " << lastEqIndex << endl;
        (*res)[lastEqIndex] = Node(canBeEqual ? Tag::T_EQUAL : Tag::T_INCOMPARABLE);
      }
      break;
    }
    case GREATER: {
      auto st = majoChain(tl1,t,0);
      res->loadFromIterator(Stack<Node>::BottomFirstIterator(st));
      break;
    }
    case LESS: {
      auto st = alphaChain(s,0,tl2);
      res->loadFromIterator(Stack<Node>::BottomFirstIterator(st));
      break;
    }
    default:
      ASSERTION_VIOLATION;
  }

  ASS(res->isNonEmpty());
  // ALWAYS(!_comparisons.getValuePtr(make_tuple(tl1,tl2),ptr));
  // ASS(!ptr);
  // *ptr = std::move(res);
  // if (res->t==Node::CONDITIONAL) {
  //   auto cn = static_cast<ConditionalNode*>(res);
  //   if (cn->eqBranch == &eqNode && cn->gtBranch == &gtNode && cn->incBranch == &incNode) {
  //     res = cn->condition;
  //   }
  // }

  // cout << "preprocessing " << tl1 << " > " << tl2 << endl;
  // cout << nodeToString(res) << endl;
  return res;
}

bool LPO::isGreater(TermList lhs, TermList rhs, const SubstApplicator* applicator, Stack<Instruction>*& instructions) const
{
  Stack<Node>* st = preprocessComparison(lhs,rhs);
  // cout << "preprocessing " << lhs << " " << rhs << endl;
  // outputNodes(*st);
  // return lpo(AppliedTerm(lhs,applicator,true),AppliedTerm(rhs,applicator,true))==GREATER;

  Stack<unsigned> conditionStack;
  for (unsigned i = 0; i < st->size();) {
    // cout << "AT " << i << " " << nodeToString(*st,i) << endl;
    switch ((*st)[i].tag) {
      case Node::Tag::T_CONDITIONAL: {
        conditionStack.push(i);
        i+=4; // jump to condition
        break;
      }
      case Node::Tag::T_COMPARISON: {
        auto s = (*st)[i+1].term;
        auto t = (*st)[i+2].term;
        auto comp = lpo(AppliedTerm(s,applicator,true),AppliedTerm(t,applicator,true));
        if (conditionStack.isEmpty()) {
          return comp==GREATER;
        }
        auto ci = conditionStack.pop();
        unsigned ci_offset;
        switch (comp) {
          case EQUAL:
            ci_offset = c_offset(Node::Tag::T_EQUAL);
            break;
          case GREATER:
            ci_offset = c_offset(Node::Tag::T_GREATER);
            break;
          case INCOMPARABLE:
            ci_offset = c_offset(Node::Tag::T_INCOMPARABLE);
            break;
          default:
            ASSERTION_VIOLATION;
        }
        i = ci+ci_offset;
        break;
      }
      case Node::Tag::T_EQUAL:
      {
        if (conditionStack.isEmpty()) {
          return false;
        }
        auto ci = conditionStack.pop();
        i = ci + c_offset(Node::Tag::T_EQUAL);
        break;
      }
      case Node::Tag::T_GREATER:
      {
        if (conditionStack.isEmpty()) {
          return true;
        }
        auto ci = conditionStack.pop();
        i = ci + c_offset(Node::Tag::T_GREATER);
        break;
      }
      case Node::Tag::T_INCOMPARABLE:
      {
        if (conditionStack.isEmpty()) {
          return false;
        }
        auto ci = conditionStack.pop();
        i = ci + c_offset(Node::Tag::T_INCOMPARABLE);
        break;
      }
      case Node::Tag::T_JUMP:
      {
        i = i + (*st)[i].offset;
        break;
      }
      case Node::Tag::T_TERM:
      {
        ASSERTION_VIOLATION;
      }
    }
  }
  ASSERTION_VIOLATION;
}

void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
