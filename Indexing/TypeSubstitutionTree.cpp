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
 * @file TypeSubstitutionTree.cpp
 * Implements class TypeSubstitutionTree.
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


namespace Indexing
{

using namespace Lib;
using namespace Kernel;

template<class LeafData_>
TypeSubstitutionTree<LeafData_>::TypeSubstitutionTree(MismatchHandler* hndlr)
: SubstitutionTree(env.signature->typeCons()), _handler(hndlr)
{}

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

template<class LeafData_>
struct TypeSubstitutionTree<LeafData_>::ToTermUnifier
{
  ToTermUnifier(TermList queryTerm, bool retrieveSubstitutions, MismatchHandler* hndlr)
  : _queryTerm(queryTerm), _retrieveSubstitutions(retrieveSubstitutions), _handler(hndlr) {}

  bool enter (const TermQueryResult<LeafData>& tqr) {
    CALL("TypeSubstitutionTree::ToTermUnifier::enter");

    if(_retrieveSubstitutions){
      RobSubstitution* subst=tqr.substitution->tryGetRobSubstitution();
      ASS(subst);
      if(_queryTerm.isVar() || tqr.data().key().isVar()){
        if(_handler){
          ASS(!tqr.data().key().isVar()); // constraints should never be variables
          if(_handler->isConstraintTerm(tqr.data().key()).maybe()){
            // term is also in the standard tree and we will unify with it there
            return false;
          }
        }
        subst->bdRecord(_bdata);
        ALWAYS(subst->unify(_queryTerm, QRS_QUERY_BANK, tqr.data().key(), QRS_RESULT_BANK));
        subst->bdDone();        
      } else {
        return subst->tryAddConstraint(_queryTerm, QRS_QUERY_BANK, tqr.data().key(), QRS_RESULT_BANK, _bdata);
      }
    }
    return true;
  }

  void leave(const TermQueryResult<LeafData>& tqr) {
    CALL("TypeSubstitutionTree::ToTermUnifier::leave");

    if(_retrieveSubstitutions){
       _bdata.backtrack();
      ASS(_bdata.isEmpty());
    }
  }

private:
  TermList _queryTerm;
  bool _retrieveSubstitutions;
  MismatchHandler* _handler;
  BacktrackData _bdata;
};

/**
 * According to value of @b insert, insert or remove leaf data.
 */
template<class LeafData_>
void TypeSubstitutionTree<LeafData_>::handleTerm(LeafData ld, bool insert)
{
  CALL("TypeSubstitutionTree::handleTerm");
  auto sort = ld.sort();

  ASS(sort.isVar() || sort.term()->isSort());

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

    Renaming normalizer;
    normalize(normalizer, ld);
    // normalizer.normalizeVariables(ld.key());

    Term* normSort=normalizer.apply(term);

    BindingMap svBindings;
    this->getBindings(normSort, svBindings);

    unsigned rootNodeIndex=getRootNodeIndex(normSort);

    if(insert) {
      SubstitutionTree::insert(&this->_nodes[rootNodeIndex], svBindings, ld);
    } else {
      SubstitutionTree::remove(&this->_nodes[rootNodeIndex], svBindings, ld);
    }
  }
}

template<class LeafData_>
TermQueryResultIterator<LeafData_> 
TypeSubstitutionTree<LeafData_>::getUnifications(TermList sort, TermList trm,bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getUnifications");

  if(sort.isOrdinaryVar()) {
    return pvi(getContextualIterator(getAllUnifyingIterator(sort,retrieveSubstitutions), 
      ToTermUnifier(trm, retrieveSubstitutions, _handler)));
  } else {
    ASS(sort.isTerm());
    auto it1 = 
      pvi(getContextualIterator(
        ldIteratorToTQRIterator(typename LDSkipList::RefIterator(_vars), sort, retrieveSubstitutions), 
        ToTermUnifier(trm, retrieveSubstitutions, _handler)));
    auto it2 = getContextualIterator(
	    getResultIterator<UnificationsIterator>(sort.term(), retrieveSubstitutions), 
        ToTermUnifier(trm, retrieveSubstitutions, _handler));
    return pvi(getConcatenatedIterator(it1, it2));     
  }
}

/**
 * Functor, that transforms &b QueryResult struct into
 * @b TermQueryResult.
 */
template<class LeafData_>
struct TypeSubstitutionTree<LeafData_>::TermQueryResultFn
{
  TermQueryResult<LeafData> operator() (const QueryResult& qr) {
    return TermQueryResult<LeafData>(*qr.first, qr.second);
  }
};

template<class LeafData_>
template<class Iterator>
TermQueryResultIterator<LeafData_> TypeSubstitutionTree<LeafData_>::getResultIterator(Term* trm,
	  bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = this->_nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions);
    }
    else{
      VirtualIterator<QueryResult> qrit=vi( new Iterator(this, root, trm, retrieveSubstitutions,false,false,_handler) );
      result = pvi( getMappingIterator(qrit, TermQueryResultFn()) );
    }
  }

  return result;
}

template<class LeafData_>
struct TypeSubstitutionTree<LeafData_>::LDToTermQueryResultFn
{
  TermQueryResult<LeafData> operator() (const LeafData& ld) {
    return TermQueryResult<LeafData>(ld);
  }
};

template<class LeafData_>
struct TypeSubstitutionTree<LeafData_>::LDToTermQueryResultWithSubstFn
{
  LDToTermQueryResultWithSubstFn(MismatchHandler* hndlr)
  {
    _subst=RobSubstitutionSP(new RobSubstitution(hndlr));
  }
  TermQueryResult<LeafData> operator() (const LeafData& ld) {
    return TermQueryResult<LeafData>(ld,
    ResultSubstitution::fromSubstitution(_subst.ptr(),
	    QRS_QUERY_BANK,QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

template<class LeafData_>
struct TypeSubstitutionTree<LeafData_>::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    CALL("TypeSubstitutionTree::LeafToLDIteratorFn()");
    return l->allChildren();
  }
};

template<class LeafData_>
struct TypeSubstitutionTree<LeafData_>::UnifyingContext
{
  UnifyingContext(TermList querySort)
  : _querySort(querySort) {}
  bool enter(TermQueryResult<LeafData> qr)
  {
    CALL("TypeSubstitutionTree::UnifyingContext::enter");

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_querySort, QRS_QUERY_BANK, qr.sort(), QRS_RESULT_BANK);
    return unified;
  }
  void leave(TermQueryResult<LeafData> qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
  }
private:
  TermList _querySort;
};

template<class LeafData_>
template<class LDIt>
TermQueryResultIterator<LeafData_> 
TypeSubstitutionTree<LeafData_>::ldIteratorToTQRIterator(LDIt ldIt,
	TermList queryTerm, bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::ldIteratorToTQRIterator");
  // only call withConstraints if we are also getting substitions, the other branch doesn't handle constraints
  //ASS(retrieveSubstitutions); 
 
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

template<class LeafData_>
TermQueryResultIterator<LeafData_> 
TypeSubstitutionTree<LeafData_>::getAllUnifyingIterator(TermList sort, bool retrieveSubstitutions)
{
  CALL("TypeSubstitutionTree::getAllUnifyingIterator");

  ASS(sort.isVar());

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  return ldIteratorToTQRIterator(
    getConcatenatedIterator(it1,typename LDSkipList::RefIterator(_vars)),
    sort, retrieveSubstitutions);
  
}


template<class LeafData_>
std::ostream& TypeSubstitutionTree<LeafData_>::output(std::ostream& out) const 
{ return out << *static_cast<SubstitutionTree const*>(this); }

}
