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

struct LPO::Node {
  enum Type {
    RESULT,
    COMPARISON,
    CONDITIONAL,
  };
  Type t;
  Node(Type t) : t(t) {}
  virtual vvector<vstring> toString() const = 0;
  virtual ~Node() = default;

  bool isResult(Result r) const;
};

vstring nodeToString(LPO::Node* n) {
  vstringstream str;
  for (const auto& line : n->toString()) {
    str << line << endl;
  }
  return str.str();
}

struct LPO::ConditionalNode : public LPO::Node {
  ConditionalNode(Node* condition, Node* eqBranch, Node* gtBranch, Node* incBranch)
    : Node(CONDITIONAL), condition(condition), eqBranch(eqBranch), gtBranch(gtBranch), incBranch(incBranch) {}

  vvector<vstring> toString() const {
    vvector<vstring> res;
    res.push_back("CONDITIONAL");
    res.push_back("  CONDITION");
    for (const auto& line : condition->toString()) {
      res.push_back("    " + line);
    }
    res.push_back("  if EQUAL");
    for (const auto& line : eqBranch->toString()) {
      res.push_back("    " + line);
    }
    res.push_back("  if GREATER");
    for (const auto& line : gtBranch->toString()) {
      res.push_back("    " + line);
    }
    res.push_back("  if INCOMPARABLE");
    for (const auto& line : incBranch->toString()) {
      res.push_back("    " + line);
    }
    return res;
  }

  Node* condition;
  Node* eqBranch;
  Node* gtBranch;
  Node* incBranch;
};

struct LPO::ResultNode : public LPO::Node {
  ResultNode(Result result) : Node(Node::RESULT), result(result) {}
  Result result;
  vvector<vstring> toString() const override { return { resultToString(result) }; }
};

bool LPO::Node::isResult(Result r) const {
  if (t != RESULT) {
    return false;
  }
  auto self = static_cast<const ResultNode*>(this);
  return self->result==r;
}

struct LPO::ComparisonNode : public LPO::Node {
  ComparisonNode(const LPO& lpo, TermList lhs, TermList rhs) : Node(Node::COMPARISON), lpo(lpo), lhs(lhs), rhs(rhs) {}
  vvector<vstring> toString() const override {
    return { lhs.toString() + " ? " + rhs.toString() };
  }
  const LPO& lpo;
  TermList lhs;
  TermList rhs;
};

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

LPO::Node* LPO::preprocessComparison(TermList tl1, TermList tl2) const
{
  Node** ptr;
  if (!_comparisons.getValuePtr(make_pair(tl1,tl2),ptr)) {
    return *ptr;
  }

  static ResultNode eqNode(EQUAL);
  static ResultNode gtNode(GREATER);
  static ResultNode incNode(INCOMPARABLE);

  auto majoChain = [this](TermList tl1, Term* t, unsigned i) -> Node* {
    ConditionalNode* curr = nullptr;
    ConditionalNode* prev = nullptr;
    Node* res = nullptr;
    for (unsigned j = i; j < t->arity(); j++) {
      auto compNode = preprocessComparison(tl1,*t->nthArgument(j));
      if (compNode->isResult(GREATER)) {
        continue;
      }
      if (compNode->isResult(EQUAL) || compNode->isResult(INCOMPARABLE)) {
        if (prev) {
          prev->gtBranch = &incNode;
        } else {
          res = &incNode;
        }
        break;
      }
      curr = new ConditionalNode(compNode,&incNode,nullptr,&incNode);
      if (prev) {
        prev->gtBranch = curr;
      } else {
        res = curr;
      }
      prev = curr;
    }
    if (!res) {
      return &gtNode;
    }
    curr->gtBranch = &gtNode;
    return res;
  };

  auto alphaChain = [this](Term* s, unsigned i, TermList tl2) -> Node* {
    ConditionalNode* curr = nullptr;
    ConditionalNode* prev = nullptr;
    Node* res = nullptr;
    for (unsigned j = i; j < s->arity(); j++) {
      auto compNode = preprocessComparison(*s->nthArgument(j),tl2);
      if (compNode->isResult(INCOMPARABLE)) {
        continue;
      }
      if (compNode->isResult(EQUAL) || compNode->isResult(GREATER)) {
        if (prev) {
          prev->incBranch = &gtNode;
        } else {
          res = &gtNode;
        }
        break;
      }
      curr = new ConditionalNode(compNode,&gtNode,&gtNode,nullptr);
      if (prev) {
        prev->incBranch = curr;
      } else {
        res = curr;
      }
      prev = curr;
    }
    if (!res) {
      return &incNode;
    }
    curr->incBranch = &incNode;
    return res;
  };

  // use compare here to filter out as many
  // precomputable comparisons as possible
  auto comp = compare(tl1,tl2);
  ASS(comp != LESS_EQ && comp != GREATER_EQ);
  if (comp != INCOMPARABLE) {
    if (comp == LESS) {
      *ptr = &incNode;
    } else if (comp == GREATER) {
      *ptr = &gtNode;
    } else {
      *ptr = &eqNode;
    }
    // *ptr = new ResultNode(comp);
    return *ptr;
  }
  if (tl1.isVar() || tl2.isVar()) {
    *ptr = new ComparisonNode(*this,tl1,tl2);
    return *ptr;
  }

  auto s = tl1.term();
  auto t = tl2.term();

  Node* res = nullptr;

  switch (comparePrecedences(s, t)) {
    case EQUAL: {
      ASS(s->arity()); // constants cannot be incomparable

      Substitution subst;
      ConditionalNode* curr = nullptr;
      ConditionalNode* prev = nullptr;

      // lexicographic comparisons
      bool canBeEqual = true;
      bool earlyReturn = false;
      for (unsigned i = 0; i < s->arity(); i++) {
        auto s_arg = SubstHelper::apply(*s->nthArgument(i),subst);
        auto t_arg = SubstHelper::apply(*t->nthArgument(i),subst);
        auto compNode = preprocessComparison(s_arg,t_arg);
        if (compNode->isResult(EQUAL)) {
          ALWAYS(unify(s_arg,t_arg,subst));
          continue;
        }

        auto majoNode = majoChain(SubstHelper::apply(tl1,subst),SubstHelper::apply(tl2,subst).term(),i+1);
        if (compNode->isResult(GREATER)) {
          if (prev) {
            prev->eqBranch = majoNode;
          } else {
            res = majoNode;
          }
          earlyReturn = true;
          break;
        }
        auto alphaNode = alphaChain(SubstHelper::apply(tl1,subst).term(),i+1,SubstHelper::apply(tl2,subst));
        if (compNode->isResult(INCOMPARABLE)) {
          if (prev) {
            prev->eqBranch = alphaNode;
          } else {
            res = alphaNode;
          }
          earlyReturn = true;
          break;
        }

        curr = new ConditionalNode(compNode,nullptr,majoNode,alphaNode);
        if (prev) {
          prev->eqBranch = curr;
        } else {
          res = curr;
        }
        prev = curr;

        if (!unify(s_arg,t_arg,subst)) {
          canBeEqual = false;
          break;
        }
      }
      if (!earlyReturn) {
        curr->eqBranch = canBeEqual ? &eqNode : &incNode;
      }
      break;
    }
    case GREATER: {
      res = majoChain(tl1,t,0);
      break;
    }
    case LESS: {
      res = alphaChain(s,0,tl2);
      break;
    }
    default:
      ASSERTION_VIOLATION;
  }

  ASS(res);
  ALWAYS(!_comparisons.getValuePtr(make_tuple(tl1,tl2),ptr));
  ASS(!*ptr);
  *ptr = res;
  if (res->t==Node::CONDITIONAL) {
    auto cn = static_cast<ConditionalNode*>(res);
    if (cn->eqBranch == &eqNode && cn->gtBranch == &gtNode && cn->incBranch == &incNode) {
      res = cn->condition;
    }
  }

  // cout << "preprocessing " << tl1 << " > " << tl2 << endl;
  // cout << nodeToString(res) << endl;
  return res;
}

bool LPO::isGreater(TermList lhs, TermList rhs, const SubstApplicator* applicator, Stack<Instruction>*& instructions) const
{
  auto n = preprocessComparison(lhs,rhs);
  Stack<ConditionalNode*> conditionStack;
  Node* curr = n;
  while (true) {
    switch (curr->t) {
      case Node::CONDITIONAL: {
        auto cn = static_cast<ConditionalNode*>(curr);
        conditionStack.push(cn);
        curr = cn->condition;
        break;
      }
      case Node::COMPARISON:
      case Node::RESULT:
      {
        Result comp;
        if (curr->t == Node::RESULT) {
          auto cn = static_cast<ResultNode*>(curr);
          comp = cn->result;
        } else {
          auto cn = static_cast<ComparisonNode*>(curr);
          comp = lpo(AppliedTerm(cn->lhs,applicator,true),AppliedTerm(cn->rhs,applicator,true));
        }
        if (conditionStack.isEmpty()) {
          return comp==GREATER;
        }
        auto cond = conditionStack.pop();
        switch (comp) {
          case EQUAL:
            curr = cond->eqBranch;
            break;
          case GREATER:
            curr = cond->gtBranch;
            break;
          case INCOMPARABLE:
            curr = cond->incBranch;
            break;
          default:
            ASSERTION_VIOLATION;
        }
        break;
      }
    }
  }
  ASSERTION_VIOLATION;
}

void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
