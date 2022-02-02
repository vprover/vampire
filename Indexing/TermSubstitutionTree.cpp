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
#include "Lib/TimeCounter.hpp"

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
: SubstitutionTree(env.signature->functions(),useC, rfSubs), _extByAbs(rfSubs)
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

  ASS(t.isTerm());
  Term* term=t.term();

  Term* normTerm=Renaming::normalize(term);

  BindingMap svBindings;
  getBindings(normTerm, svBindings);

  unsigned rootNodeIndex=getRootNodeIndex(normTerm);

  SubstitutionTree::insert(&_nodes[rootNodeIndex], svBindings, ld);  
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
    getBindings(normTerm, svBindings);

    unsigned rootNodeIndex=getRootNodeIndex(normTerm);

    if(insert) {
      SubstitutionTree::insert(&_nodes[rootNodeIndex], svBindings, ld);
    } else {
      SubstitutionTree::remove(&_nodes[rootNodeIndex], svBindings, ld);
    }
  }
}

TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions,false);
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
    auto it1 = sortVar || sortArrow ? _funcSubtermsByType->getUnifications(sort, t, retrieveSubstitutions):
               TermQueryResultIterator::getEmpty();
    auto it2 = sortVar || sortAtomic ? getAllUnifyingIterator(t,retrieveSubstitutions,false):
               TermQueryResultIterator::getEmpty();
    return pvi(getConcatenatedIterator(it1, it2));
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
    return getAllUnifyingIterator(t,retrieveSubstitutions,false);
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
  unsigned rootIndex=getRootNodeIndex(trm);
  Node* root=_nodes[rootIndex];
  if(!root) {
    return false;
  }
  if(root->isLeaf()) {
    return true;
  }
  // Currently we do not need to generate constraints with generalisations
  // FastGeneralizationsIterator does not support constraints anyway
  bool useC = false; 
  return FastGeneralizationsIterator(this, root, trm, false,false,false,useC).hasNext();
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
    return getAllUnifyingIterator(t,retrieveSubstitutions,false);
  } else {
    ASS(t.isTerm());
    return getResultIterator<FastInstancesIterator>(t.term(), retrieveSubstitutions,false);
  }
}

/**
 * Functor, that transforms &b QueryResult struct into
 * @b TermQueryResult.
 */
struct TermSubstitutionTree::TermQueryResultFn
{
  TermQueryResultFn(bool extra = false){
    _extra = extra;
  }

  TermQueryResult operator() (const QueryResult& qr) {
    TermList trm = _extra ? qr.first.first->extraTerm : qr.first.first->term;
    return TermQueryResult(trm, qr.first.first->literal,
	    qr.first.first->clause, qr.first.second,qr.second);
  }

private:
  bool _extra;
};

template<class Iterator>
TermQueryResultIterator TermSubstitutionTree::getResultIterator(Term* trm,
	  bool retrieveSubstitutions,bool withConstraints)
{
  CALL("TermSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = _nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions,false);
    }
    else{
      VirtualIterator<QueryResult> qrit=vi( new Iterator(this, root, trm, retrieveSubstitutions,false,false, 
                                                         withConstraints, 
                                                         (_extByAbs ? &_functionalSubtermMap : 0) ));
      result = pvi( getMappingIterator(qrit, TermQueryResultFn(_extra)) );
    }
  }

  // DO NOT ALLOW UNIFICATIONS AT THE TOP LEVEL
  if(false){
    ASS(retrieveSubstitutions);
    // this true means that I am allowed to pass a non-variable term to getAllUnifyingIterator
    TermQueryResultIterator other = getAllUnifyingIterator(TermList(trm),retrieveSubstitutions,true); 
    result = pvi(getConcatenatedIterator(result,other));
  }
  return result;
}

struct TermSubstitutionTree::LDToTermQueryResultFn
{
  TermQueryResult operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct TermSubstitutionTree::LDToTermQueryResultWithSubstFn
{
  LDToTermQueryResultWithSubstFn(bool wc) : _withConstraints(wc)
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
    _constraints=UnificationConstraintStackSP(new Stack<UnificationConstraint>());
  }
  TermQueryResult operator() (const LeafData& ld) {
    if(_withConstraints){
      return TermQueryResult(ld.term, ld.literal, ld.clause,
            ResultSubstitution::fromSubstitution(_subst.ptr(),
                    QRS_QUERY_BANK,QRS_RESULT_BANK),
            _constraints);
    }
    else{
      return TermQueryResult(ld.term, ld.literal, ld.clause,
	    ResultSubstitution::fromSubstitution(_subst.ptr(),
		    QRS_QUERY_BANK,QRS_RESULT_BANK));
    }
  }
private:
  bool _withConstraints;
  RobSubstitutionSP _subst;
  UnificationConstraintStackSP _constraints;
};

struct TermSubstitutionTree::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    CALL("TermSubstitutionTree::LeafToLDIteratorFn()");
    return l->allChildren();
  }
};

struct TermSubstitutionTree::UnifyingContext
{
  UnifyingContext(TermList queryTerm,bool withConstraints)
  : _queryTerm(queryTerm)
#if VDEBUG
    , _withConstraints(withConstraints)
#endif
  {}
  bool enter(TermQueryResult qr)
  {
    //if(_withConstraints){ cout << "enter " << qr.term << endl; }

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_queryTerm, QRS_QUERY_BANK, qr.term, QRS_RESULT_BANK);
    //unsigned srt;
    ASS(unified || _withConstraints);
    return unified;
  }
  void leave(TermQueryResult qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
    if(!qr.constraints.isEmpty()){
      //cout << "reset constraints" << endl;
      qr.constraints->reset();
    }
  }
private:
  TermList _queryTerm;
#if VDEBUG
  bool _withConstraints;
#endif
};

template<class LDIt>
TermQueryResultIterator TermSubstitutionTree::ldIteratorToTQRIterator(LDIt ldIt,
	TermList queryTerm, bool retrieveSubstitutions,bool withConstraints)
{
  CALL("TermSubstitutionTree::ldIteratorToTQRIterator");
  // only call withConstraints if we are also getting substitions, the other branch doesn't handle constraints
  ASS(retrieveSubstitutions | !withConstraints); 

  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldIt,
		    LDToTermQueryResultWithSubstFn(withConstraints)),
	    UnifyingContext(queryTerm,withConstraints)) );
  } else {
    return pvi( getMappingIterator(
	    ldIt,
	    LDToTermQueryResultFn()) );
  }
}

TermQueryResultIterator TermSubstitutionTree::getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions,bool withConstraints)
{
  CALL("TermSubstitutionTree::getAllUnifyingIterator");

  //if(withConstraints){ cout << "getAllUnifyingIterator for " << trm.toString() << endl; }

  ASS(trm.isVar() || withConstraints);

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  // If we are searching withConstraints it means that we have already added in
  // the results related to _vars, we are only interested in non-unifying leaves

  // STOP DOING THIS AT THE TOP LEVEL
  if(false){
    return ldIteratorToTQRIterator(it1,trm, retrieveSubstitutions,withConstraints);
  }
  else{
    return ldIteratorToTQRIterator(
	    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
	    trm, retrieveSubstitutions,withConstraints);
  }
}


}
