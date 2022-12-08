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
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Options.hpp"

#include "TermSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TermSubstitutionTree::TermSubstitutionTree(bool useC, bool rfSubs, bool extra)
: SubstitutionTree(useC, rfSubs), _extByAbs(rfSubs)
{
  _extra = extra;
  if(rfSubs){
    _funcSubtermsByType = new TypeSubstitutionTree();
  }
}

void TermSubstitutionTree::insert(TermList t, TermList trm)
{ handleTerm(t, LeafData(0, 0, t, trm), /* insert */ true); }

void TermSubstitutionTree::insert(TermList t, TermList trm, Literal* lit, Clause* cls)
{ handleTerm(t, LeafData(cls, lit, t, trm), /* insert */ true); }

void TermSubstitutionTree::insert(TermList t, Literal* lit, Clause* cls)
{ handleTerm(t, LeafData(cls,lit,t), /* insert */ true); }

void TermSubstitutionTree::remove(TermList t, Literal* lit, Clause* cls)
{ handleTerm(t, LeafData(cls,lit,t), /* insert */ false); }

/**
 * According to value of @b insert, insert or remove term.
 */
void TermSubstitutionTree::handleTerm(TermList t, LeafData ld, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");

  if(_extByAbs && t.isTerm()){ 
    TermList sort = SortHelper::getResultSort(t.term());
    if(sort.isVar() || sort.isArrowSort()){
      _funcSubtermsByType->handleTerm(sort, ld, insert);
      if(sort.isArrowSort()){ return; }
    } 
  }


  auto normTerm = Renaming::normalize(t);

  if(_extByAbs){
    normTerm = ApplicativeHelper::replaceFunctionalAndBooleanSubterms(normTerm, &_functionalSubtermMap);   
  }

  BindingMap svBindings;


  SubstitutionTree::createInitialBindings(normTerm, /* reversed */ false, /* withoutTop */ false, 
      [&](auto var, auto term) { 
        svBindings.insert(var, term);
        _nextVar = max(_nextVar, (int)var + 1);
      });

  if(insert) {
    SubstitutionTree::insert(svBindings, ld);
  } else {
    SubstitutionTree::remove(svBindings, ld);
  }
}

TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  return getResultIterator<UnificationsIterator>(t, retrieveSubstitutions, /* useConstraints */ false);
}

TermQueryResultIterator TermSubstitutionTree::getUnificationsWithConstraints(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsWithConstraints");
  return getResultIterator<UnificationsIterator>(t, retrieveSubstitutions, /* useConstraints */ true);
}

//higher-order concern
TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TermList t, TermList sort, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsUsingSorts");

  ASS(_extByAbs);

  bool sortVar = sort.isVar();
  bool sortArrow = sort.isArrowSort();
  bool sortAtomic = !sortVar && !sortArrow;

  //TODO Is it OK to use t below?

  auto it2 = sortVar || sortArrow ? _funcSubtermsByType->getUnifications(sort, t, retrieveSubstitutions) :
             TermQueryResultIterator::getEmpty();
  auto it3 = sortVar || sortAtomic ? getResultIterator<UnificationsIterator>(t, retrieveSubstitutions,false):
             TermQueryResultIterator::getEmpty();
  return pvi(getConcatenatedIterator(it2, it3));
}


bool TermSubstitutionTree::generalizationExists(TermList t)
{
  if(!t.isTerm()) {
    return false;
  }
  if(!_root) {
    return false;
  }
  if(_root->isLeaf()) {
    return true;
  }
  return FastGeneralizationsIterator(this, _root, t, false,false,false, /* useC */ false).hasNext();
}

/**
 * Return iterator, that yields generalizations of the given term.
 */
TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  return getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions,false);
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  return getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions,false);
}

// TODO get rid of this method
template<class Iterator, class TermOrLit>
TermQueryResultIterator TermSubstitutionTree::getResultIterator(TermOrLit trm, bool retrieveSubstitutions,bool withConstraints)
{ return SubstitutionTree::iterator<Iterator>(trm, retrieveSubstitutions, withConstraints, _extra, (_extByAbs ? &_functionalSubtermMap : nullptr)); }

}
