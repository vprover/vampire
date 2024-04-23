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
    JUNCTION,
    COMPARISON,
  };
  Type t;
  Node(Type t) : t(t) {}
  virtual bool execute(const SubstApplicator* applicator) const = 0;
  virtual vvector<vstring> toString() const = 0;
  virtual ~Node() = default;
};

struct ResultNode : public LPO::Node {
  ResultNode(bool result) : Node(Node::RESULT), result(result) {}
  bool result;
  bool execute(const SubstApplicator* applicator) const override { return result; }
  vvector<vstring> toString() const override { return { result ? "true" : "false" }; }
};

struct JunctionNode : public LPO::Node {
  enum JunctionType {
    CONJUNCTION,
    DISJUNCTION,
  };
  JunctionNode(JunctionType jt) : Node(Node::JUNCTION), jt(jt) {}
  bool execute(const SubstApplicator* applicator) const override {
    if (jt==CONJUNCTION) {
      for (const auto& ch : children) {
        if (!ch->execute(applicator)) {
          return false;
        }
      }
      return true;
    } else {
      for (const auto& ch : children) {
        if (ch->execute(applicator)) {
          return true;
        }
      }
      return false;
    }
  }
  static Node* create(JunctionType jt, vvector<Node*>&& children) {
    for (unsigned i = 0; i < children.size();) {
      if (children[i]->t!=Node::RESULT) {
        i++;
        continue;
      }
      auto rn = static_cast<ResultNode*>(children[i]);
      if (rn->result==(jt==CONJUNCTION)) {
        swap(children[i],children.back());
        children.pop_back();
        continue;
      }
      return new ResultNode(rn->result);
    }
    if (children.empty()) {
      return new ResultNode(jt==CONJUNCTION);
    }
    if (children.size()==1) {
      return children[0];
    }
    auto res = new JunctionNode(jt);
    res->children = children;
    return res;
  }
  vvector<vstring> toString() const override {
    vvector<vstring> res;
    res.push_back(jt==CONJUNCTION ? "AND" : "OR");
    for (const auto& ch : children) {
      for (const auto& line : ch->toString()) {
        res.push_back("  " + line);
      }
    }
    return res;
  }
  JunctionType jt;
  vvector<Node*> children;
};

struct ComparisonNode : public LPO::Node {
  // ComparisonNode() = default;
  ComparisonNode(const LPO& lpo, Ordering::Result t, TermList lhs, TermList rhs) : Node(Node::COMPARISON), lpo(lpo), type(t), lhs(lhs), rhs(rhs) {}
  bool execute(const SubstApplicator* applicator) const override {
    return lpo.compare(AppliedTerm(lhs,applicator,true),AppliedTerm(rhs,applicator,true))==type;
  }
  vvector<vstring> toString() const override {
    return { lhs.toString() + " " + Ordering::resultToString(type) + " " + rhs.toString() };
  }
  const LPO& lpo;
  Ordering::Result type;
  TermList lhs;
  TermList rhs;
};

LPO::Node* LPO::preprocessComparison(TermList tl1, TermList tl2, Result expected) const
{
  // cout << "preprocessing " << tl1 << " > " << tl2 << endl;

  Node** ptr;
  if (!_comparisons.getValuePtr(make_tuple(tl1,tl2,expected),ptr)) {
    return *ptr;
  }

  auto comp = compare(tl1,tl2);
  if (comp != INCOMPARABLE) {
    *ptr = new ResultNode(comp == expected);
    return *ptr;
  }
  if (tl1.isVar() || tl2.isVar()) {
    *ptr = new ComparisonNode(*this,expected,tl1,tl2);
    return *ptr;
  }

  auto s = tl1.term();
  auto t = tl2.term();

  if (expected==EQUAL)
  {
    if (s->functor()!=t->functor()) {
      *ptr = new ResultNode(false);
      return *ptr;
    }
    vvector<Node*> subres;
    bool equal = true;
    SubtermIterator sstit(s);
    SubtermIterator tstit(t);
    while (sstit.hasNext()) {
      ALWAYS(tstit.hasNext());
      auto sst = sstit.next();
      auto tst = tstit.next();
      if (sst == tst) {
        sstit.right();
        tstit.right();
        continue;
      }

      if (sst.isVar() || tst.isVar()) {
        subres.push_back(new ComparisonNode(*this,EQUAL,sst,tst));
        sstit.right();
        tstit.right();
        continue;
      }
      if (sst.term()->functor()!=tst.term()->functor()) {
        equal = false;
        break;
      }
    }
    if (equal) {
      auto res = new JunctionNode(JunctionNode::CONJUNCTION);
      *ptr = res;
      res->children = std::move(subres);
      return *ptr;
    } else {
      for (const auto& n : subres) {
        delete n;
      }
      *ptr = new ResultNode(false);
      return *ptr;
    }

  } else {
    Substitution subst;
    auto bind = [&subst](Node* n) {
      if (n->t!=Node::COMPARISON) {
        return;
      }
      auto cn = static_cast<ComparisonNode*>(n);
      if (cn->type!=EQUAL) {
        return;
      }
      if (cn->lhs.isVar() || cn->rhs.isVar()) {
        auto eqLHS = cn->lhs.isVar() ? cn->lhs : cn->rhs;
        auto eqRHS = cn->lhs.isVar() ? cn->rhs : cn->lhs;
        subst.bind(eqLHS.var(),eqRHS);
      }
    };
    auto apply = [&subst](TermList t) {
      return SubstHelper::apply(t,subst);
    };
    switch (comparePrecedences(s, t)) {
      case EQUAL: {
        ASS(s->arity()); // constants cannot be incomparable

        vvector<Node*> subres;

        // lexicographic comparisons
        for (unsigned i = 0; i < s->arity(); i++) {
          vvector<Node*> subsubres;
          for (unsigned j = 0; j < i; j++) {
            subsubres.push_back(preprocessComparison(apply(*s->nthArgument(j)),apply(*t->nthArgument(j)),EQUAL));
            bind(subsubres.back());
          }
          subsubres.push_back(preprocessComparison(apply(*s->nthArgument(i)),apply(*t->nthArgument(i)),GREATER));
          bind(subsubres.back());
          for (unsigned j = i+1; j < s->arity(); j++) {
            subsubres.push_back(preprocessComparison(apply(tl1),apply(*t->nthArgument(j)),GREATER));
            bind(subsubres.back());
          }
          subres.push_back(JunctionNode::create(JunctionNode::CONJUNCTION,std::move(subsubres)));
        }
        // alpha comparisons
        for (unsigned i = 0; i < s->arity(); i++) {
          subres.push_back(preprocessComparison(*s->nthArgument(i),tl2,GREATER));
          subres.push_back(preprocessComparison(*s->nthArgument(i),tl2,EQUAL));
        }

        auto res = JunctionNode::create(JunctionNode::DISJUNCTION,std::move(subres));
        ALWAYS(!_comparisons.getValuePtr(make_tuple(tl1,tl2,expected),ptr));
        ASS(!*ptr);
        *ptr = res;
        return res;
      }
      case GREATER: {
        vvector<Node*> subres;
        for (unsigned i = 0; i < t->arity(); i++) {
          subres.push_back(preprocessComparison(apply(tl1),apply(*t->nthArgument(i)),GREATER));
          bind(subres.back());
        }
        auto res = JunctionNode::create(JunctionNode::CONJUNCTION,std::move(subres));
        ALWAYS(!_comparisons.getValuePtr(make_tuple(tl1,tl2,expected),ptr));
        ASS(!*ptr);
        *ptr = res;
        return res;
      }
      case LESS: {
        vvector<Node*> subres;
        for (unsigned i = 0; i < s->arity(); i++) {
          subres.push_back(preprocessComparison(*s->nthArgument(i),tl2,GREATER));
          subres.push_back(preprocessComparison(*s->nthArgument(i),tl2,EQUAL));
        }
        auto res = JunctionNode::create(JunctionNode::DISJUNCTION,std::move(subres));
        ALWAYS(!_comparisons.getValuePtr(make_tuple(tl1,tl2,expected),ptr));
        ASS(!*ptr);
        *ptr = res;
        return res;
      }
      default:
        ASSERTION_VIOLATION;
    }
  }

}

bool LPO::isGreater(AppliedTerm lhs, AppliedTerm rhs) const
{
  // return lpo(std::move(lhs),std::move(rhs))==GREATER;
  ASS_EQ(lhs.applicator,rhs.applicator);
  ASS(lhs.aboveVar);
  ASS(rhs.aboveVar);
  auto n = preprocessComparison(lhs.term,rhs.term,GREATER);
  // cout << "isGreater " << lhs << " " << rhs << endl;
  // for (const auto& line : n->toString()) {
  //   cout << line << endl;
  // }
  // cout << endl;
  return n->execute(lhs.applicator);
}

void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
