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

bool LPO::isGreater(TermList lhs, TermList rhs, const std::function<TermList(TermList)>& applicator) const
{
  return isGreaterOrEq(AppliedTermLPO(lhs,applicator,true),AppliedTermLPO(rhs,applicator,true),applicator)==GREATER;
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


struct ComparisonNode {
  ComparisonNode() = default;
  ComparisonNode(Ordering::Result t, TermList lhs, TermList rhs) : type(t), lhs(lhs), rhs(rhs) {}

  Ordering::Result type;
  TermList lhs;
  TermList rhs;
  Vector<ComparisonNode>* alternative = nullptr;
};

using CompVec = Vector<ComparisonNode>;
using CompStack = Stack<ComparisonNode>;

vstring typeToString(Ordering::Result t) {
  switch(t) {
    case Ordering::GREATER:
      return ">";
    // case ComparisonNode::GE:
    //   return ">=";
    case Ordering::EQUAL:
      return "=";
    default:
      ASSERTION_VIOLATION;
  }
}

ostream& operator<<(ostream& out, const ComparisonNode& n) {
  out << n.lhs << " " << typeToString(n.type) << " " << n.rhs;
  return out;
}

void outputComparisons(Vector<ComparisonNode>* root)
{
  static Stack<tuple<Vector<ComparisonNode>*,unsigned,unsigned>> todo;
  todo.push(make_tuple(root,0,0));

  while(todo.isNonEmpty()) {
    auto [vec,index,depth] = todo.pop();
    auto curr = (*vec)[index];

    if (curr.alternative) {
      todo.push(make_tuple(curr.alternative,0,depth+1));
    }
    if (index+1 < vec->length()) {
      todo.push(make_tuple(vec,index+1,depth));
    }
    for (unsigned i = 0; i < depth; i++) {
      cout << "  ";
    }
    cout << curr << endl;
  }
}

void replaceWithChain(const CompStack& chain, CompVec*& ptr, unsigned index)
{
  // cout << "replaceWithChain" << endl;
  // for (const auto& n : chain) {
  //   cout << n << endl;
  // }
  // cout << endl;
  ASS(ptr);
  ASS_L(index,ptr->length());
  auto newptr = CompVec::allocate(chain.size()+ptr->length()-1);
  for (unsigned j = 0; j < index; j++) {
    (*newptr)[j] = (*ptr)[j];
  }
  for (unsigned j = 0; j < chain.size(); j++) {
    (*newptr)[j+index] = chain[j];
  }
  for (unsigned j = index+1; j < ptr->length(); j++) {
    (*newptr)[j+chain.size()] = (*ptr)[j];
  }
  ptr->deallocate();
  ptr = newptr;
}

void incorporateChain(const CompStack& chain, CompVec*& ptr)
{
  // cout << "incorporateChain" << endl;
  // for (const auto& n : chain) {
  //   cout << n << endl;
  // }
  // cout << endl;
  ASS(!ptr);
  ptr = CompVec::allocate(chain.size());
  for (unsigned i = 0; i < chain.size(); i++) {
    (*ptr)[i] = chain[i];
  }
}

void deallocateSubtrees(CompVec*& ptr, unsigned index)
{
  Stack<CompVec*> todo;
  for (unsigned i = index; i < ptr->length(); i++) {
    todo.push((*ptr)[i].alternative);
  }
  while (todo.isNonEmpty()) {
    auto curr = todo.pop();
    if (!curr) {
      continue;
    }
    for (unsigned i = 0; i < curr->length(); i++) {
      todo.push((*curr)[i].alternative);
    }
    curr->deallocate();
  }
}

void removeFalseElement(CompVec*& ptr, unsigned index)
{
  int prevAltIndex = -1;
  for (int i = index; i >= 0; i--) {
    if ((*ptr)[i].alternative) {
      prevAltIndex = i;
      break;
    }
  }
  // cout << "prevAltIndex " << prevAltIndex << endl;
  if (prevAltIndex == -1) {
    // no alternative, delete entire vector
    deallocateSubtrees(ptr, 0);
    ptr->deallocate();
    ptr = nullptr;
  } else {
    deallocateSubtrees(ptr, prevAltIndex+1);
    auto other = (*ptr)[prevAltIndex].alternative;
    ASS(other);
    auto newSize = max(prevAltIndex+other->length(),ptr->length());
    // cout << "newSize " << newSize << endl;
    if (newSize > ptr->length()) {
      auto newPtr = CompVec::allocate(newSize);
      for (unsigned i = 0; i < prevAltIndex; i++) {
        (*newPtr)[i] = (*ptr)[i];
      }
      ptr->deallocate();
      ptr = newPtr;
    }
    for (unsigned i = 0; i < other->length(); i++) {
      (*ptr)[prevAltIndex+i] = (*other)[i];
    }
    other->deallocate();
  }
}

void LPO::preprocessComparison(TermList tl1, TermList tl2) const
{
  cout << "preprocessing " << tl1 << " > " << tl2 << endl;

  auto rootVec = CompVec::allocate(1);
  (*rootVec)[0] = ComparisonNode(GREATER, tl1, tl2);
  // stack of (chain, index) pairs
  Stack<reference_wrapper<CompVec*>> todo;
  todo.push(ref(rootVec));

  while (todo.isNonEmpty()) {
    auto vec = todo.pop();
    for (unsigned index = 0; index < (*vec).length();) {
      // cout << "index " << index << " " << (*vec).length() << endl;
      auto curr = (*vec)[index];
      // cout << "subcase " << curr.lhs << " " << typeToString(curr.type) << " " << curr.rhs << endl;
      auto comp = compare(curr.lhs,curr.rhs);
      if (comp != INCOMPARABLE) {
        if (comp != curr.type) {
          // cout << "removing" << endl;
          removeFalseElement(vec, index);
          // cout << "after removal" << endl;
          // outputComparisons(rootVec);
          // cout << endl;
          if (!vec) {
            break;
          }
        } else {
          // remove true element
          index++;
        }
        continue;
      }
      if (curr.lhs.isVar() || curr.rhs.isVar()) {
        // cout << "compare " << curr.lhs << " " << curr.rhs << endl;
        index++;
        continue;
      }
      auto s = curr.lhs.term();
      auto t = curr.rhs.term();

      if (curr.type==EQUAL) {
        if (s->functor()==t->functor()) {
          Stack<ComparisonNode> chain;
          for (unsigned i = 0; i < s->arity(); i++) {
            chain.push(ComparisonNode(EQUAL,*s->nthArgument(i),*t->nthArgument(i)));
          }
          replaceWithChain(chain, vec, index);
        } else {
          removeFalseElement(vec, index);
          if (!vec) {
            break;
          }
        }
      } else {
        auto currVec = vec;
        auto currIndex = index;
        switch (comparePrecedences(s, t)) {
          case EQUAL: {
            // cout << "lexMAE" << endl;
            ASS(s->arity()); // constants cannot be incomparable

            // lexicographic comparisons
            for (unsigned i = 0; i < s->arity(); i++) {
              Stack<ComparisonNode> chain;
              for (unsigned j = 0; j < i; j++) {
                chain.push(ComparisonNode(EQUAL,*s->nthArgument(j),*t->nthArgument(j)));
              }
              chain.push(ComparisonNode(GREATER,*s->nthArgument(i),*t->nthArgument(i)));
              for (unsigned j = i+1; j < s->arity(); j++) {
                chain.push(ComparisonNode(GREATER,curr.lhs,*t->nthArgument(j)));
              }

              if (i==0) {
                replaceWithChain(chain, currVec, currIndex);
              } else {
                incorporateChain(chain, (*currVec)[currIndex].alternative);
                currVec = (*currVec)[currIndex].alternative;
                currIndex = 0;
              }
            }
            // alpha comparisons
            for (unsigned i = 0; i < s->arity(); i++) {
              Stack<ComparisonNode> chain;
              chain.push(ComparisonNode(GREATER,*s->nthArgument(i),curr.rhs));
              incorporateChain(chain, (*currVec)[currIndex].alternative);
              currVec = (*currVec)[currIndex].alternative;
              currIndex = 0;

              chain.reset();
              chain.push(ComparisonNode(EQUAL,*s->nthArgument(i),curr.rhs));
              incorporateChain(chain, (*currVec)[currIndex].alternative);
              currVec = (*currVec)[currIndex].alternative;
              currIndex = 0;
            }
            break;
          }
          case GREATER: {
            // cout << "majo" << endl;
            Stack<ComparisonNode> chain;
            for (unsigned i = 0; i < s->arity(); i++) {
              chain.push(ComparisonNode(GREATER,curr.lhs,*t->nthArgument(i)));
            }
            replaceWithChain(chain, currVec, currIndex);
            break;
          }
          default: {
            // cout << "alpha" << endl;
            for (unsigned i = 0; i < s->arity(); i++) {
              Stack<ComparisonNode> chain;
              chain.push(ComparisonNode(GREATER,*s->nthArgument(i),curr.rhs));

              if (i==0) {
                replaceWithChain(chain, currVec, currIndex);
              } else {
                incorporateChain(chain, (*currVec)[currIndex].alternative);
                currVec = (*currVec)[currIndex].alternative;
                currIndex = 0;
              }

              chain.reset();
              chain.push(ComparisonNode(EQUAL,*s->nthArgument(i),curr.rhs));
              incorporateChain(chain, (*currVec)[currIndex].alternative);
              currVec = (*currVec)[currIndex].alternative;
              currIndex = 0;
            }
            break;
          }
        }
      }
      // outputComparisons(rootVec);
      // cout << endl;
    }
    if (!vec) {
      continue;
    }
    for (unsigned index = 0; index < (*vec).length(); index++) {
      if ((*vec)[index].alternative) {
        todo.push(ref((*vec)[index].alternative));
      }
    }
  }
  outputComparisons(rootVec);
  cout << endl;
}



void LPO::showConcrete(ostream&) const 
{ /* lpo is fully defined by the precedence relation */ }

}
