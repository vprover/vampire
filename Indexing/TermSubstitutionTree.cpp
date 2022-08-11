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

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

template<class LeafData_>
TermSubstitutionTree<LeafData_>::TermSubstitutionTree(MismatchHandler* hndlr)
: SubstitutionTree(env.signature->functions()), _handler(hndlr)
{
  if(_handler){
    _constraintTerms = new TypeSubstitutionTree(_handler);
  }
}


// template<class LeafData_>
// void TermSubstitutionTree<LeafData_>::remove(TermList t, Literal* lit, Clause* cls)
// {
//   CALL("TermSubstitutionTree::remove");
//   handleTerm(t, LeafData(cls, lit, t), false);
// }

/**
 * According to value of @b insert, insert or remove term.
 */
template<class LeafData_>
void TermSubstitutionTree<LeafData_>::handleTerm(LeafData ld, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");
  auto t = ld.key();

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
    this->getBindings(normTerm, svBindings);

    unsigned rootNodeIndex=getRootNodeIndex(normTerm);

    if(insert) {
      SubstitutionTree::insert(&this->_nodes[rootNodeIndex], svBindings, ld);
    } else {
      SubstitutionTree::remove(&this->_nodes[rootNodeIndex], svBindings, ld);
    }
  }
}

template<class LeafData_>
bool TermSubstitutionTree<LeafData_>::constraintTermHandled(TermList t, LeafData ld, bool insert){
  CALL("TermSubstitutionTree::constraintTermHandled");

  ASS(_handler);

  auto res = _handler->isConstraintTerm(t);
  if(!res.isFalse()){
    _constraintTerms->handleTerm(ld, insert);
    // if it is only possibly a constraint term, we still want to insert
    // it into the standard tree as well
    if(!res.maybe())
      return true;
  }
  return false;
}

template<class LeafData_>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::getUnifications(TermList t,
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
	      ldIteratorToTQRIterator(typename LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
	      getResultIterator<UnificationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}

//higher-order concern
template<class LeafData_>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::getUnificationsUsingSorts(TermList t, TermList sort,
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
    auto it1 = ldIteratorToTQRIterator(typename LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);

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


template<class LeafData_>
bool TermSubstitutionTree<LeafData_>::generalizationExists(TermList t)
{
  if(!_vars.isEmpty()) {
    return true;
  }
  if(!t.isTerm()) {
    return false;
  }
  Term* trm=t.term();
  unsigned rootIndex=getRootNodeIndex(trm);
  Node* root = this->_nodes[rootIndex];
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
template<class LeafData_>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::getGeneralizations(TermList t,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  if(t.isOrdinaryVar()) {
    //only variables generalize other variables
    return ldIteratorToTQRIterator(typename LDSkipList::RefIterator(_vars), t, retrieveSubstitutions);
  } else {
    ASS(t.isTerm());
    if(_vars.isEmpty()) {
      return getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions);
    } else {
      return pvi( getConcatenatedIterator(
	      ldIteratorToTQRIterator(typename LDSkipList::RefIterator(_vars), t, retrieveSubstitutions),
	      getResultIterator<FastGeneralizationsIterator>(t.term(), retrieveSubstitutions)) );
    }
  }
}

template<class LeafData_>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::getInstances(TermList t,
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
template<class LeafData_>
struct TermSubstitutionTree<LeafData_>::TermQueryResultFn
{
  template<class LD>
  TermQueryResult<LeafData> specializedOperator(LD*, const QueryResult& qr)  {
    return TermQueryResult<LeafData>(*qr.first, qr.second);
  }

  TermQueryResult<LeafData> operator() (const QueryResult& qr) {
    return specializedOperator((LeafData*) nullptr, qr);
  }
};

template<class LeafData_>
template<class Iterator>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::getResultIterator(Term* trm,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getResultIterator");

  //cout << "getResultIterator " << trm->toString() << endl;

  TermQueryResultIterator result = TermQueryResultIterator::getEmpty();
  
  Node* root = this->_nodes[getRootNodeIndex(trm)];

  if(root){
    if(root->isLeaf()) {
      LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
      result = ldIteratorToTQRIterator(ldit,TermList(trm),retrieveSubstitutions);
    }
    else{
      VirtualIterator<QueryResult> qrit=vi( 
        new Iterator(this, root, trm, retrieveSubstitutions,false,false, _handler));
      result = pvi( getMappingIterator(qrit, TermQueryResultFn()) );
    }
  }

  return result;
}

template<class LeafData_>
struct TermSubstitutionTree<LeafData_>::LDToTermQueryResultFn
{
  TermQueryResult<LeafData> operator() (const LeafData& ld) {
    return TermQueryResult<LeafData>(ld);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

template<class LeafData_>
struct TermSubstitutionTree<LeafData_>::LDToTermQueryResultWithSubstFn
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
struct TermSubstitutionTree<LeafData_>::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    CALL("TermSubstitutionTree::LeafToLDIteratorFn()");
    return l->allChildren();
  }
};

template<class LeafData_>
struct TermSubstitutionTree<LeafData_>::UnifyingContext
{
  UnifyingContext(TermList queryTerm)
  : _queryTerm(queryTerm)
  {}
  bool enter(TermQueryResult<LeafData> const& qr)
  {
    CALL("TermSubstitutionTree::UnifyingContext::enter");

    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    bool unified = subst->unify(_queryTerm, QRS_QUERY_BANK, qr.key(), QRS_RESULT_BANK);
    ASS(unified);
    return unified;
  }
  void leave(TermQueryResult<LeafData> const& qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
  }
private:
  TermList _queryTerm;
};

template<class LeafData_>
template<class LDIt>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::ldIteratorToTQRIterator(LDIt ldIt,
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

template<class LeafData_>
TermQueryResultIterator<LeafData_> TermSubstitutionTree<LeafData_>::getAllUnifyingIterator(TermList trm,
	  bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getAllUnifyingIterator");
  ASS(trm.isVar());

  auto it1 = getFlattenedIterator(getMappingIterator(vi( new LeafIterator(this) ), LeafToLDIteratorFn()));

  return ldIteratorToTQRIterator(
    getConcatenatedIterator(it1,typename LDSkipList::RefIterator(_vars)),
    trm, retrieveSubstitutions);
}

template<class LeafData_>
std::ostream& TermSubstitutionTree<LeafData_>::output(std::ostream& out) const 
{ return out << *static_cast<SubstitutionTree const*>(this); }

}
