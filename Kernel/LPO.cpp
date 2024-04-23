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

#include "Indexing/ResultSubstitution.hpp"
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

Ordering::Result LPO::comparePrecedences(Term* t1, Term* t2) const
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
  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    return tl2.containsSubterm(tl1) ? LESS : INCOMPARABLE;
  }
  ASS(tl1.isTerm());
  return clpo(tl1.term(), tl2);
}

Ordering::Result LPO::clpo(Term* t1, TermList tl2) const
{
  ASS(t1->shared());

  if(tl2.isOrdinaryVar()) {
    return t1->containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }
  
  ASS(tl2.isTerm());
  Term* t2=tl2.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return cLMA(t1, t2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return cMA(t1, t2->args(), t2->arity());
  case LESS:
    return Ordering::reverse(cMA(t2, t1->args(), t1->arity()));
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
Ordering::Result LPO::cMA(Term *s, TermList* tl, unsigned arity) const
{
  ASS(s->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch(clpo(s, *(tl - i))) {
    case EQUAL:
    case LESS:
      return LESS;
    case INCOMPARABLE:
      return reverse(alpha(tl - i - 1, arity - i - 1, s));
    case GREATER:
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return GREATER;
}

Ordering::Result LPO::cLMA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const
{
  ASS(s->shared());
  ASS(t->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch(compare(*(sl - i), *(tl - i))) {
    case EQUAL:
      break;
    case GREATER:
      return cMA(s, tl - i - 1, arity - i - 1);
    case LESS:
      return reverse(cMA(t, sl - i - 1, arity - i - 1));
    case INCOMPARABLE:
      return cAA(s, t, sl - i - 1, tl - i - 1, arity - i - 1, arity - i - 1);
    default:
      ASSERTION_VIOLATION;
    }
  }
  return EQUAL;
}

Ordering::Result LPO::cAA(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity1, unsigned arity2) const
{
  ASS(s->shared());
  ASS(t->shared());

  switch (alpha(sl, arity1, t)) {
  case GREATER:
    return GREATER;
  case INCOMPARABLE:
    return reverse(alpha(tl, arity2, s));
  default:
    ASSERTION_VIOLATION;
  }
}

// greater iff some exists s_i in sl such that s_i >= t 
Ordering::Result LPO::alpha(TermList* sl, unsigned arity, Term *t) const
{
  ASS(t->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch (lpo(*(sl - i), TermList(t))) {
    case EQUAL:
    case GREATER:
      return GREATER;
    case LESS:
    case INCOMPARABLE:
      break;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return INCOMPARABLE;
}

// unidirectional comparison function (returns correct result if tl1 >
// tl2 or tl1 = tl2)
Ordering::Result LPO::lpo(TermList tl1, TermList tl2) const
{
  if(tl1==tl2) {
    return EQUAL;
  }
  if(tl1.isOrdinaryVar()) {
    return INCOMPARABLE;
  }
  ASS(tl1.isTerm());
  Term* t1 = tl1.term();
  ASS(t1->shared());

  if(tl2.isOrdinaryVar()) {
    return t1->containsSubterm(tl2) ? GREATER : INCOMPARABLE;
  }

  ASS(tl2.isTerm());
  Term* t2=tl2.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return lexMAE(t1, t2, t1->args(), t2->args(), t1->arity());
  case GREATER:
    return majo(t1, t2->args(), t2->arity());
  default:
    return alpha(t1->args(), t1->arity(), t2);
  }
}

Ordering::Result LPO::lexMAE(Term* s, Term* t, TermList* sl, TermList* tl, unsigned arity) const
{
  ASS(s->shared());
  ASS(t->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch (lpo(*(sl - i), *(tl - i))) {
    case EQUAL:
      break;
    case GREATER:
      return majo(s, tl - i - 1, arity - i - 1);
    case INCOMPARABLE:
      return alpha(sl - i - 1, arity - i - 1, t);
    default:
      ASSERTION_VIOLATION;
    }
  }
  // reached only when the terms are equal but this is checked already
  // at the start of LPO::lpo, which is the only caller of this function
  ASSERTION_VIOLATION;
}

// greater if s is greater than every term in tl
Ordering::Result LPO::majo(Term* s, TermList* tl, unsigned arity) const
{
  ASS(s->shared());

  for (unsigned i = 0; i < arity; i++) {
    switch(lpo(TermList(s), *(tl - i))) {
    case GREATER:
      break;
    case EQUAL:
    case INCOMPARABLE:
      return INCOMPARABLE;
    default:
      ASSERTION_VIOLATION;
    }
  }
  return GREATER;
}

// isGreater variants

template<class Applicator>
bool containsVar(const AppliedTermLPO<Applicator>& s, TermList var, const Applicator& applicator)
{
  ASS(var.isVar());
  if (!s.termAboveVar) {
    return s.term.containsSubterm(var);
  }
  if (s.term.isVar()) {
    return applicator(s.term).containsSubterm(var);
  }
  VariableIterator vit(s.term.term());
  while (vit.hasNext()) {
    auto v = vit.next();
    if (applicator(v).containsSubterm(var)) {
      return true;
    }
  }
  return false;
}

template<class Applicator>
Ordering::Result LPO::isGreaterOrEq(AppliedTermLPO<Applicator>&& tt1, AppliedTermLPO<Applicator>&& tt2, const Applicator& applicator) const
{
  // cout << endl << "isGreaterOrEq " << tt1.term << " " << tt2.term << endl;
  if (tt1==tt2) {
    return EQUAL;
  }
  if (tt1.term.isOrdinaryVar()) {
    return INCOMPARABLE;
  }
  // if (tt2.term.isOrdinaryVar()) {
  //   return containsVar(tt1, tt2.term, applicator) ? GREATER : INCOMPARABLE;
  // }
  ASS(tt1.term.isTerm());
  return clpo_gt(tt1, tt2, applicator) ? GREATER : INCOMPARABLE;
}

using BRApplicator = Indexing::BoundResultApplicator;
using BQApplicator = Indexing::BoundQueryApplicator;

template Ordering::Result LPO::isGreaterOrEq<BRApplicator>(AppliedTermLPO<BRApplicator>&&, AppliedTermLPO<BRApplicator>&&, const BRApplicator&) const;
template Ordering::Result LPO::isGreaterOrEq<BQApplicator>(AppliedTermLPO<BQApplicator>&&, AppliedTermLPO<BQApplicator>&&, const BQApplicator&) const;
template Ordering::Result LPO::isGreaterOrEq<IdentityApplicator>(AppliedTermLPO<IdentityApplicator>&&, AppliedTermLPO<IdentityApplicator>&&, const IdentityApplicator&) const;

template<class Applicator>
bool LPO::clpo_gt(AppliedTermLPO<Applicator> tt1, AppliedTermLPO<Applicator> tt2, const Applicator& applicator) const
{
  // cout << "clpo_gt " << tt1.term << " " << tt2.term << endl;
  ASS(tt1.term.isTerm());

  if (tt2.term.isOrdinaryVar()) {
    return containsVar(tt1, tt2.term, applicator);
  }

  Term* t1=tt1.term.term();
  Term* t2=tt2.term.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return lexMAE_gt(tt1, tt2, t1->args(), t2->args(), t1->arity(), applicator);
  case GREATER:
    return majo_gt(tt1, t2->args(), t2->arity(), tt2.termAboveVar, applicator);
  case LESS:
    return alpha_gt(t1->args(), t1->arity(), tt1.termAboveVar, tt2, applicator);
  default:
    ASSERTION_VIOLATION;
  }
}

// greater iff some exists s_i in sl such that s_i >= t
template<class Applicator>
bool LPO::alpha_gt(TermList* sl, unsigned arity, bool argsAboveVar, AppliedTermLPO<Applicator> t, const Applicator& applicator) const
{
  // cout << "alpha_gt " << t.term << " " << endl;
  ASS(t.term.isTerm());
  for (unsigned i = 0; i < arity; i++) {
    AppliedTermLPO s(*(sl - i),applicator,argsAboveVar);
    // cout << "alpha compare " << s.term << " " << t.term << endl;
    if (s == t || lpo_gt(s, t, applicator)) {
      return true;
    }
  }
  return false;
}

template<class Applicator>
bool LPO::lpo_gt(AppliedTermLPO<Applicator> tt1, AppliedTermLPO<Applicator> tt2, const Applicator& applicator) const
{
  // cout << "lpo_gt " << tt1.term << " " << tt2.term << endl;

  ASS(tt1!=tt2); // we want to check this outside

  if (tt1.term.isVar()) {
    return false;
  }

  if (tt2.term.isVar()) {
    return containsVar(tt1, tt2.term, applicator);
  }


  Term* t1=tt1.term.term();
  Term* t2=tt2.term.term();

  switch (comparePrecedences(t1, t2)) {
  case EQUAL:
    return lexMAE_gt(tt1, tt2, t1->args(), t2->args(), t1->arity(), applicator);
  case GREATER:
    return majo_gt(tt1, t2->args(), t2->arity(), tt2.termAboveVar, applicator);
  default:
    return alpha_gt(t1->args(), t1->arity(), tt1.termAboveVar, tt2, applicator);
  }
}

template<class Applicator>
bool LPO::lexMAE_gt(AppliedTermLPO<Applicator> s, AppliedTermLPO<Applicator> t, TermList* sl, TermList* tl, unsigned arity, const Applicator& applicator) const
{
  // cout << "lexMAE_gt " << s.term << " " << t.term << endl;

  for (unsigned i = 0; i < arity; i++) {
    // implement deep equals
    AppliedTermLPO sArg(*(sl - i),applicator,s.termAboveVar);
    AppliedTermLPO tArg(*(tl - i),applicator,t.termAboveVar);
    // cout << "lex compare " << sArg.term << " " << tArg.term << endl;
    if (sArg == tArg) {
      // cout << "equal" << endl;
      continue;
    }
    // cout << "not equal" << endl;
    if (lpo_gt(sArg, tArg, applicator)) {
      return majo_gt(s, tl - i - 1, arity - i - 1, t.termAboveVar, applicator);
    } else {
      return alpha_gt(sl - i - 1, arity - i - 1, s.termAboveVar, t, applicator);
    }
  }
  // reached only when the terms are equal but this is checked already
  // at the start of LPO::lpo, which is the only caller of this function
  ASSERTION_VIOLATION;
}

// greater if s is greater than every term in tl
template<class Applicator>
bool LPO::majo_gt(AppliedTermLPO<Applicator> s, TermList* tl, unsigned arity, bool argsAboveVar, const Applicator& applicator) const
{
  // cout << "majo_gt " << s.term << endl;

  for (unsigned i = 0; i < arity; i++) {
    AppliedTermLPO t(*(tl - i), applicator, argsAboveVar);
    // cout << "majo compare " << s.term << " " << t.term << endl;
    if (s == t || !lpo_gt(s, t, applicator)) {
      return false;
    }
  }
  return true;
}

using Applicator = std::function<TermList(TermList)>;

struct LPO::Node {
  enum Type {
    RESULT,
    JUNCTION,
    COMPARISON,
  };
  Type t;
  Node(Type t) : t(t) {}
  virtual bool execute(const Applicator& applicator) const = 0;
  virtual vvector<vstring> toString() const = 0;
  virtual ~Node() = default;
};

struct ResultNode : public LPO::Node {
  ResultNode(bool result) : Node(Node::RESULT), result(result) {}
  bool result;
  bool execute(const Applicator& applicator) const override { return result; }
  vvector<vstring> toString() const override { return { result ? "true" : "false" }; }
};

struct JunctionNode : public LPO::Node {
  enum JunctionType {
    CONJUNCTION,
    DISJUNCTION,
  };
  JunctionNode(JunctionType jt) : Node(Node::JUNCTION), jt(jt) {}
  bool execute(const Applicator& applicator) const override {
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
  bool execute(const Applicator& applicator) const override {
    return lpo.compare(applicator(lhs),applicator(rhs))==type;
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

bool LPO::isGreater(TermList lhs, TermList rhs, const std::function<TermList(TermList)>& applicator) const
{
  // return isGreaterOrEq(AppliedTermLPO(lhs,applicator,true),AppliedTermLPO(rhs,applicator,true),applicator)==GREATER;
  auto n = preprocessComparison(lhs,rhs,GREATER);
  // cout << "isGreater " << lhs << " " << rhs << endl;
  // for (const auto& line : n->toString()) {
  //   cout << line << endl;
  // }
  // cout << endl;
  return n->execute(applicator);
}



void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
