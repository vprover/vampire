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
#include "Shell/UnificationWithAbstractionConfig.hpp"

#include "TermSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TermSubstitutionTree::TermSubstitutionTree(bool theoryConstraints, bool hoConstraints, bool extra)
: SubstitutionTree(env.signature->functions()), 
  _theoryConstraints(theoryConstraints),
  _higherOrderConstraints(hoConstraints)
{
  _extra = extra;
  _withConstraints = _higherOrderConstraints || _theoryConstraints;
  // at the moment, unification with abstraction for theory reasoning
  // and higher-order are not compatible.
  ASS(!(_higherOrderConstraints && _theoryConstraints));
  if(_withConstraints){
    _termsByType = new TypeSubstitutionTree();
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

  if(constraintTermHandled(t, ld, insert)) return;

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

    if(_higherOrderConstraints){
      t = ApplicativeHelper::replaceFunctionalAndBooleanSubterms(normTerm, &_termMap);   
      normTerm = t.term();
    }

    if(_theoryConstraints){
      // replace theory subterms by very special variables
      // For example f($sum(X,Y), b) ---> f(#, b)
      TheoryTermReplacement ttr(&_termMap);
      normTerm = ttr.transform(normTerm);
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

bool TermSubstitutionTree::constraintTermHandled(TermList t, LeafData ld, bool insert){
  CALL("TermSubstitutionTree::constraintTermHandled");

  if(!_withConstraints) return false;
  if(!t.isTerm()) return false;

  auto trm = t.term();
  auto sort = SortHelper::getResultSort(trm);
  
  if(_higherOrderConstraints){ 
    if(sort.isVar() || sort.isArrowSort()){
      _termsByType->handleTerm(sort, ld, insert);
      // In the case where the sort is a variable
      // we want to also insert term into the normal tree
      // since it could have non-function type depending
      // on type instantiation
      if(sort.isArrowSort()){ return true; }
    } 
  }

  if(_theoryConstraints){
    if( Shell::UnificationWithAbstractionConfig::isInterpreted(trm) &&
       !Shell::UnificationWithAbstractionConfig::isNumeral(t)){
      _termsByType->handleTerm(sort, ld, insert);
      return true;    
    }    
  }

  return false;
}


TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnifications");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      // false here means without constraints
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
          // false here means without constraints
	  ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
          // false here means without constraints
	  getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}

//higher-order concern
TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TermList t, TermList sort,
    bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsUsingSorts");
  ASS(_withConstraints);

  if(t.isOrdinaryVar()) {
    auto it1 = _termsByType->getUnifications(sort, t, retrieveSubstitutions);
    // in the case of a variable of higher-order sort (e.g. X : i > i > i)
    // we do not want to unify with all terms in the tree only to subsequently
    // fail the typing check (since all terms of sort i > i > i will be in _termsByType)
    auto it2 = !sort.isArrowSort() ? 
                  getAllUnifyingIterator(t,retrieveSubstitutions):
                  ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);;
    return pvi(getConcatenatedIterator(it1, it2));
  } else {
    ASS(t.isTerm());
    //TODO Is it OK to use t below?
    auto it1 = _vars.isEmpty() ? TermQueryResultIterator::getEmpty() :
               ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);

    bool addConstraints = 
      (Shell::UnificationWithAbstractionConfig::isInterpreted(t.term()) &&
      !Shell::UnificationWithAbstractionConfig::isNumeral(t)) ||
      env.options->unificationWithAbstraction() != Shell::Options::UnificationWithAbstraction::INTERP_ONLY;

    auto it2 = addConstraints ?
      _termsByType->getUnifications(sort, t, retrieveSubstitutions) :
      TermQueryResultIterator::getEmpty();
    auto it3 = getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions);
    return pvi(getConcatenatedIterator(getConcatenatedIterator(it1, it2), it3));
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

  return FastGeneralizationsIterator(this, root, trm, false,false,false).hasNext();
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
    return ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      return getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
	      ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
	      getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  if(t.isOrdinaryVar()) {
    return getAllUnifyingIterator(t,retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    return getResultIterator<FastInstancesIterator>(t.term(), retrieveSubstitutions);
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
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = _nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions);
    }
    else{
      auto cType = NO_CONSTRAINTS;
      if(_withConstraints){
        if(_theoryConstraints) cType = THEORY_CONSTRAINTS;
        if(_higherOrderConstraints) cType = HO_CONSTRAINTS;
      }

      VirtualIterator<QueryResult> qrit=vi( 
        new Iterator(this, root, trm, retrieveSubstitutions,false,false, cType, &_termMap));
      result = pvi( getMappingIterator(qrit, TermQueryResultFn(_extra)) );
    }
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
  LDToTermQueryResultWithSubstFn()
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  TermQueryResult operator() (const LeafData& ld) {
    // see no harm in always adding an empty constraint
    return TermQueryResult(ld.term, ld.literal, ld.clause,
          ResultSubstitution::fromSubstitution(_subst.ptr(),
                  QRS_QUERY_BANK,QRS_RESULT_BANK), UnificationConstraintStackSP());
  }
private:
  RobSubstitutionSP _subst;
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
  UnifyingContext(TermList queryTerm)
  : _queryTerm(queryTerm)
  {}

  bool enter(TermQueryResult qr)
  {
    CALL("TermSubstitutionTree::UnifyingContext::enter");
    //if(_withConstraints){ cout << "enter " << qr.term << endl; }

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_queryTerm, QRS_QUERY_BANK, qr.term, QRS_RESULT_BANK);
    ASS(unified);
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
};

template<class LDIt>
TermQueryResultIterator TermSubstitutionTree::ldIteratorToTQRIterator(LDIt ldIt,
	TermList queryTerm, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::ldIteratorToTQRIterator");

  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldIt,
		    LDToTermQueryResultWithSubstFn()),
	    UnifyingContext(queryTerm)) );
  } else {
    return pvi( getMappingIterator(
	    ldIt,
	    LDToTermQueryResultFn()) );
  }
}

TermQueryResultIterator TermSubstitutionTree::getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getAllUnifyingIterator");
  ASS(trm.isVar())

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  // If we are searching withConstraints it means that we have already added in
  // the results related to _vars, we are only interested in non-unifying leaves

  // STOP DOING THIS AT THE TOP LEVEL
  if(false){
    return ldIteratorToTQRIterator(it1,trm, retrieveSubstitutions);
  }
  else{
    return ldIteratorToTQRIterator(
	    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
	    trm, retrieveSubstitutions);
  }
}


}
