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

TermSubstitutionTree::TermSubstitutionTree(MismatchHandler* hndlr, bool extra)
: SubstitutionTree(env.signature->functions()), _handler(hndlr), _extra(extra)
{
  if(_handler){
    _constraintTerms = new TypeSubstitutionTree(_handler);
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

  if(_handler && constraintTermHandled(t, ld, insert)) return;

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
    if(_handler){
      normTerm = _handler->transform(normTerm);
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

  ASS(_handler);

  auto res = _handler->isConstraintTerm(t);
  if(!res.isFalse()){
    auto sort = SortHelper::getResultSort(t.term()); 
    _constraintTerms->handleTerm(sort, ld, insert);
    // if it is only possibly a constraint term, we still want to insert
    // it into the standard tree as well
    if(!res.maybe())
      return true;
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
      return getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
	      ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
	      getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}

//higher-order concern
TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TermList t, TermList sort,
    bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getUnificationsUsingSorts");

  if(t.isOrdinaryVar()) {
    // get all constraint terms whose sort can be unified with @param sort
    // constraint terms that are also in the standard tree are not included
    auto it1 = _constraintTerms->getUnifications(sort, t, retrieveSubstitutions);

    auto it2 = getAllUnifyingIterator(t,retrieveSubstitutions);
    
    return pvi(getConcatenatedIterator(it1, it2));
  } else {
    ASS(t.isTerm());
    // get all variables
    auto it1 = ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);

    // get top level constraints
    // if @param t can play no part in constraints, we optimise
    auto it2 = !_handler->isConstraintTerm(t).isFalse() ?
       _constraintTerms->getUnifications(sort, t, retrieveSubstitutions) :
       TermQueryResultIterator::getEmpty();

    // get unifiers from standard tree
    // again we optimise and avoid uselessly traversing the tree
    auto it3 = !_handler->isConstraintTerm(t).isTrue() ?
       getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions) :
       TermQueryResultIterator::getEmpty();

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
    TermList trm = _extra ? qr.first->extraTerm : qr.first->term;
    return TermQueryResult(trm, qr.first->literal,
	    qr.first->clause, qr.second);
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
      VirtualIterator<QueryResult> qrit=vi( 
        new Iterator(this, root, trm, retrieveSubstitutions,false,false, _handler));
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
  LDToTermQueryResultWithSubstFn(MismatchHandler* hndlr)
  {
    _subst=RobSubstitutionSP(new RobSubstitution(hndlr));
  }
  TermQueryResult operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause,
          ResultSubstitution::fromSubstitution(_subst.ptr(),
                  QRS_QUERY_BANK,QRS_RESULT_BANK));
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
		    LDToTermQueryResultWithSubstFn(_handler)),
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

  return ldIteratorToTQRIterator(
    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
    trm, retrieveSubstitutions);
}


}
