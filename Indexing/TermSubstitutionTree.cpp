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
{
  CALL("TermSubstitutionTree::insert(TermList)");

  ASS(t.isTerm());
  LeafData ld(0, 0, t, trm);
  insert(t, ld);
}

void TermSubstitutionTree::insert(TermList t, TermList trm, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::insert(TermList)");

  LeafData ld(cls, lit, t, trm);
  insert(t, ld);
}

void TermSubstitutionTree::insert(TermList t, LeafData ld)
{
  CALL("TermSubstitutionTree::insert");
  // TODO make this and handleTerm one function!!

  ASS(t.isTerm());
  Term* term=t.term();

  Term* normTerm=Renaming::normalize(term);

  BindingMap svBindings;
  svBindings.insert(0, TermList(normTerm));
  _nextVar = max(_nextVar, 1);

  SubstitutionTree::insert(svBindings, ld);  
}


void TermSubstitutionTree::insert(TermList t, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::insert");
  handleTerm(t,lit,cls, true);
}

void TermSubstitutionTree::remove(TermList t, Literal* lit, Clause* cls)
{
  CALL("TermSubstitutionTree::remove");
  handleTerm(t,lit,cls, false);
}

/**
 * According to value of @b insert, insert or remove term.
 */
void TermSubstitutionTree::handleTerm(TermList t, Literal* lit, Clause* cls, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");

  LeafData ld(cls, lit, t);

  if(_extByAbs && t.isTerm()){ 
    TermList sort = SortHelper::getResultSort(t.term());
    if(sort.isVar() || sort.isArrowSort()){
      _funcSubtermsByType->handleTerm(sort, ld, insert);
      if(sort.isArrowSort()){ return; }
    } 
  }

  if(t.isOrdinaryVar()) {
    if(insert) {
      _vars.insert(ld);
    } else {
      // why is this case needed?
      _vars.remove(ld);
    }
  } else {
    ASS(t.isTerm());
    Term* term=t.term();

    Term* normTerm=Renaming::normalize(term);

    if(_extByAbs){
      t = ApplicativeHelper::replaceFunctionalAndBooleanSubterms(normTerm, &_functionalSubtermMap);   
      normTerm = t.term();
    }

    BindingMap svBindings;
    svBindings.insert(0, TermList(normTerm));
    _nextVar = max(_nextVar, 1);

    if(insert) {
      SubstitutionTree::insert(svBindings, ld);
    } else {
      SubstitutionTree::remove(svBindings, ld);
    }
  }
}

TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  if(t.isOrdinaryVar()) {
    ASSERTION_VIOLATION_REP("TODO")
    // return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      // false here means without constraints
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,false);
    } else {
      return pvi( getConcatenatedIterator(
          // false here means without constraints
	  ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false),
          // false here means without constraints
	  getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,false)) );
    }
  }
}

//higher-order concern
TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TermList t, TermList sort,
    bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsUsingSorts");

  ASS(_extByAbs);

  bool sortVar = sort.isVar();
  bool sortArrow = sort.isArrowSort();
  bool sortAtomic = !sortVar && !sortArrow;

  if(t.isOrdinaryVar()) {

    ASSERTION_VIOLATION_REP("TODO")
    // auto it1 = sortVar || sortArrow ? _funcSubtermsByType->getUnifications(sort, t, retrieveSubstitutions):
    //            TermQueryResultIterator::getEmpty();
    // auto it2 = sortVar || sortAtomic ? getAllUnifyingIterator(t,retrieveSubstitutions,false):
    //            TermQueryResultIterator::getEmpty();
    // return pvi(getConcatenatedIterator(it1, it2));
    //TODO vars?
  } else {
    ASS(t.isTerm());
    //TODO Is it OK to use t below?
    auto it1 = _vars.isEmpty() ? TermQueryResultIterator::getEmpty() :
               ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false);

    auto it2 = sortVar || sortArrow ? _funcSubtermsByType->getUnifications(sort, t, retrieveSubstitutions) :
               TermQueryResultIterator::getEmpty();
    auto it3 = sortVar || sortAtomic ? getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,false):
               TermQueryResultIterator::getEmpty();
    return pvi(getConcatenatedIterator(getConcatenatedIterator(it1, it2), it3));
  }
}

//TODO code sharing with getUnifications
TermQueryResultIterator TermSubstitutionTree::getUnificationsWithConstraints(TermList t,
          bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsWithConstraints");

  //cout << "getUnificationsWithConstraints of " << t.toString() << endl;

  // don't need to do anything different in the case of t being a variable
  if(t.isOrdinaryVar()) {
    ASSERTION_VIOLATION_REP("TODO")
    // return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      // true here means with constraints
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,true);
    } else {
      return pvi( getConcatenatedIterator(
          //we use false here as we are giving variables so no constraints will be needed
          ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false),
          //true here means with constraints
          getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions,true)) );
    }
  }
}


bool TermSubstitutionTree::generalizationExists(TermList t)
{
  if(!_vars.isEmpty()) {
    return true;
  }
  if(!t.isTerm()) {
    return false;
  }
  Term* trm=t.term();
  if(!_root) {
    return false;
  }
  if(_root->isLeaf()) {
    return true;
  }
  // Currently we do not need to generate constraints with generalisations
  // FastGeneralizationsIterator does not support constraints anyway
  bool useC = false; 
  return FastGeneralizationsIterator(this, _root, trm, false,false,false,useC).hasNext();
}

/**
 * Return iterator, that yields generalizations of the given term.
 */
TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  if(t.isOrdinaryVar()) {
    //only variables generalize other variables
    return ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      return getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions,false);
    } else {
      return pvi( getConcatenatedIterator(
	      ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions,false),
	      getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions,false)) );
    }
  }
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  if(t.isOrdinaryVar()) {
    ASSERTION_VIOLATION_REP("TODO")
    // return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    return getResultIterator<FastInstancesIterator>(t.term(), retrieveSubstitutions,false);
  }
}

// TODO get rid of this method
template<class Iterator>
TermQueryResultIterator TermSubstitutionTree::getResultIterator(Term* trm, bool retrieveSubstitutions,bool withConstraints)
{
  return SubstitutionTree::iterator<Iterator>(trm, retrieveSubstitutions, withConstraints, _extra, 
      (_extByAbs ? &_functionalSubtermMap : nullptr));
}

// TermQueryResultIterator TermSubstitutionTree::getAllUnifyingIterator(TermList trm,
// 	  bool retrieveSubstitutions,bool withConstraints)
// {
//   CALL("TermSubstitutionTree::getAllUnifyingIterator");
//
//   //if(withConstraints){ cout << "getAllUnifyingIterator for " << trm.toString() << endl; }
//
//   ASS(trm.isVar() || withConstraints);
//
//   auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), [](auto & l){ return l->allChildren(); }));
//
//   // If we are searching withConstraints it means that we have already added in
//   // the results related to _vars, we are only interested in non-unifying leaves
//
//   // STOP DOING THIS AT THE TOP LEVEL
//   if(false){
//     return ldIteratorToTQRIterator(it1,trm, retrieveSubstitutions,withConstraints);
//   }
//   else{
//     return ldIteratorToTQRIterator(
// 	    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
// 	    trm, retrieveSubstitutions,withConstraints);
//   }
// }


}
