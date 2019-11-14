
/*
 * File TypeSubstitutionTree.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file TypeSubstitutionTree.cpp
 * Implements class TypeSubstitutionTree.
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

#include "TypeSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TypeSubstitutionTree::TypeSubstitutionTree()
: SubstitutionTree(env.signature->functions())
{
}

void TypeSubstitutionTree::insert(TermList sort, LeafData ld)
{
  CALL("TypeSubstitutionTree::insert");
  handleTerm(sort,ld,true);
}

void TypeSubstitutionTree::remove(TermList sort, LeafData ld)
{
  CALL("TypeSubstitutionTree::remove");
  handleTerm(sort,ld,false);
}

/**
 * According to value of @b insert, insert or remove term.
 */
void TypeSubstitutionTree::handleTerm(TermList sort, LeafData ld, bool insert)
{
  CALL("TypeSubstitutionTree::handleTerm");

  if(sort.isOrdinaryVar()) {
    if(insert) {
      _vars.insert(ld);
    } else {
      // why is this case needed?
      _vars.remove(ld);
    }
  }  else {
    ASS(sort.isTerm());
    Term* term=sort.term();

    Term* normTerm=Renaming::normalize(term);

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

//TODO use sorts and delete non-shared
TermQueryResultIterator TypeSubstitutionTree::getUnifications(TermList sort,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getUnifications");
  if(sort.isOrdinaryVar()) { //TODO return vars as well?
    return getAllUnifyingIterator(sort,retrieveSubstitutions);
  } else {
    ASS(sort.isTerm());
    if(_vars.isEmpty()) {
      return getResultIterator<UnificationsIterator>(sort.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
	  ldIteratorToTQRIterator(LDSkipList::RefIterator(_vars), sort, retrieveSubstitutions),
	  getResultIterator<UnificationsIterator>(sort.term(), retrieveSubstitutions)) );
    }
  }
}

/**
 * Functor, that transforms &b QueryResult struct into
 * @b TermQueryResult.
 */
struct TypeSubstitutionTree::TermQueryResultFn
{
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const QueryResult& qr) {
    return TermQueryResult(qr.first.first->term, qr.first.first->literal,
	    qr.first.first->clause, qr.first.second,qr.second, true);
  }
};

template<class Iterator>
TermQueryResultIterator TypeSubstitutionTree::getResultIterator(Term* trm,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = _nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions);
    }
    else{
      VirtualIterator<QueryResult> qrit=vi( new Iterator(this, root, trm, retrieveSubstitutions,false,false,false) );
      result = pvi( getMappingIterator(qrit, TermQueryResultFn()) );
    }
  }

  return result;
}

struct TypeSubstitutionTree::LDToTermQueryResultFn
{
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct TypeSubstitutionTree::LDToTermQueryResultWithSubstFn
{
  LDToTermQueryResultWithSubstFn()
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  DECL_RETURN_TYPE(TermQueryResult);
  OWN_RETURN_TYPE operator() (const LeafData& ld) {
    return TermQueryResult(ld.term, ld.literal, ld.clause,
    ResultSubstitution::fromSubstitution(_subst.ptr(),
	    QRS_QUERY_BANK,QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

struct TypeSubstitutionTree::LeafToLDIteratorFn
{
  DECL_RETURN_TYPE(LDIterator);
  OWN_RETURN_TYPE operator() (Leaf* l) {
    CALL("TypeSubstitutionTree::LeafToLDIteratorFn()");
    return l->allChildren();
  }
};

struct TypeSubstitutionTree::UnifyingContext
{
  UnifyingContext(TermList queryTerm)
  : _queryTerm(queryTerm) {}
  bool enter(TermQueryResult qr)
  {
    //if(_withConstraints){ cout << "enter " << qr.term << endl; }

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_queryTerm, QRS_QUERY_BANK, qr.term, QRS_RESULT_BANK);
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
TermQueryResultIterator TypeSubstitutionTree::ldIteratorToTQRIterator(LDIt ldIt,
	TermList queryTerm, bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::ldIteratorToTQRIterator");
  // only call withConstraints if we are also getting substitions, the other branch doesn't handle constraints
  ASS(retrieveSubstitutions); 

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

TermQueryResultIterator TypeSubstitutionTree::getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getAllUnifyingIterator");

  //if(withConstraints){ cout << "getAllUnifyingIterator for " << trm.toString() << endl; }

  ASS(trm.isVar());

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  // If we are searching withConstraints it means that we have already added in
  // the results related to _vars, we are only interested in non-unifying leaves

  return ldIteratorToTQRIterator(
    getConcatenatedIterator(it1,LDSkipList::RefIterator(_vars)),
    trm, retrieveSubstitutions);
  
}




}
