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
 * @file Matcher.cpp
 * Implements class Matcher.
 */

#include "Lib/DHMap.hpp"

#include "Matcher.hpp"
#include "SubstHelper.hpp"

namespace Kernel
{

using namespace std;

/**
 * Obtain a substitution by matching @b matchedInstance onto @b matchedBase
 * and return @b resultBase after application of that substitution
 *
 * @b matchedInstance must match onto @b matchedBase.
 */
TermList MatchingUtils::getInstanceFromMatch(TermList matchedBase,
    TermList matchedInstance, TermList resultBase)
{
  static Substitution subst;
  subst.reset();

  ALWAYS( matchTerms(matchedBase, matchedInstance, subst) );
  return SubstHelper::apply(resultBase, subst);
}

Formula* MatchingUtils::getInstanceFromMatch(Literal* matchedBase,
      Literal* matchedInstance, Formula* resultBase)
{
  static Substitution subst;
  subst.reset();

  ALWAYS( match(matchedBase, matchedInstance, false, subst) );
  return SubstHelper::apply(resultBase, subst);
}

bool MatchingUtils::isVariant(Literal* l1, Literal* l2, bool complementary)
{
  if(l1->isTwoVarEquality() && l2->isTwoVarEquality()){
    TermList s1 = l1->twoVarEqSort();
    TermList s2 = l2->twoVarEqSort();
    if(s1.isVar() && s2.isVar()){}
    else if(s1.isTerm() && s2.isTerm()){
      if(s1.term()->functor() != s2.term()->functor() ||
        !haveVariantArgs(s1.term(), s2.term())){
        return false;
      }
    }else{
      return false;
    }
  }
  if(!Literal::headersMatch(l1,l2,complementary)) {
    return false;
  }
  if(!complementary && l1==l2) {
    return true;
  }
  if(l1->isEquality()) {
    return haveVariantArgs(l1,l2) || haveReversedVariantArgs(l1,l2);
  } else {
    return haveVariantArgs(l1,l2);
  }
}

bool MatchingUtils::haveReversedVariantArgs(Term* l1, Term* l2)
{
  ASS_EQ(l1->arity(), 2);
  ASS_EQ(l2->arity(), 2);

  static DHMap<unsigned,unsigned,IdentityHash,DefaultHash> leftToRight;
  static DHMap<unsigned,unsigned,IdentityHash,DefaultHash> rightToLeft;
  leftToRight.reset();
  rightToLeft.reset();

  TermList s1, s2;
  bool sortUsed = false;
  if(l1->isLiteral() && static_cast<Literal*>(l1)->isTwoVarEquality())
  {
    if(l2->isLiteral() && static_cast<Literal*>(l2)->isTwoVarEquality()){
       s1 = SortHelper::getEqualityArgumentSort(static_cast<Literal*>(l1));
       s2 = SortHelper::getEqualityArgumentSort(static_cast<Literal*>(l2));
       sortUsed = true;
    } else {
      return false;
    }
  }

  auto it1 = concatIters(
      vi( new DisagreementSetIterator(*l1->nthArgument(0),*l2->nthArgument(1)) ),
      vi( new DisagreementSetIterator(*l1->nthArgument(1),*l2->nthArgument(0)) ));

  VirtualIterator<pair<TermList, TermList> > dsit =
  sortUsed ? pvi(concatIters(vi(new DisagreementSetIterator(s1,s2)), std::move(it1))) :
             pvi(std::move(it1));

  while(dsit.hasNext()) {
    pair<TermList,TermList> dp=dsit.next(); //disagreement pair
    if(!dp.first.isVar() || !dp.second.isVar()) {
  return false;
    }
    unsigned left=dp.first.var();
    unsigned right=dp.second.var();
    if(right!=leftToRight.findOrInsert(left,right)) {
  return false;
    }
    if(left!=rightToLeft.findOrInsert(right,left)) {
  return false;
    }
  }
  if(leftToRight.size()!=rightToLeft.size()) {
    return false;
  }

  return true;
}

bool MatchingUtils::haveVariantArgs(Term* l1, Term* l2)
{
  ASS_EQ(l1->arity(), l2->arity());

  if(l1==l2) {
    return true;
  }

  static DHMap<unsigned,unsigned,IdentityHash,DefaultHash> leftToRight;
  static DHMap<unsigned,unsigned,IdentityHash,DefaultHash> rightToLeft;
  leftToRight.reset();
  rightToLeft.reset();

  DisagreementSetIterator dsit(l1,l2);
  while(dsit.hasNext()) {
    pair<TermList,TermList> dp=dsit.next(); //disagreement pair
    if(!dp.first.isVar() || !dp.second.isVar()) {
  return false;
    }
    unsigned left=dp.first.var();
    unsigned right=dp.second.var();
    if(right!=leftToRight.findOrInsert(left,right)) {
  return false;
    }
    if(left!=rightToLeft.findOrInsert(right,left)) {
  return false;
    }
  }
  if(leftToRight.size()!=rightToLeft.size()) {
    return false;
  }

  return true;
}

bool MatchingUtils::matchReversedArgs(Literal* base, Literal* instance)
{
  ASS_EQ(base->arity(), 2);
  ASS_EQ(instance->arity(), 2);

  static Substitution subst;
  subst.reset();

  return matchReversedArgs(base, instance, subst);
}

bool MatchingUtils::matchArgs(Term* base, Term* instance)
{
  static Substitution subst;
  subst.reset();

  return matchArgs(base, instance, subst);
}

bool MatchingUtils::matchTerms(TermList base, TermList instance)
{
  if(base.isTerm()) {
    if(!instance.isTerm()) {
  return false;
    }

    Term* bt=base.term();
    Term* it=instance.term();
    if(bt->functor()!=it->functor()) {
      return false;
    }
    if(bt->shared() && it->shared()) {
      if(bt->ground()) {
        return bt==it;
      }
      if(bt->weight() > it->weight()) {
        return false;
      }
    }
    ASS_G(base.term()->arity(),0);
    return matchArgs(bt, it);
  } else {
    return true;
  }
}

}
