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
 * @file LiteralSubstitutionTree.cpp
 * Implements class LiteralSubstitutionTree.
 */

namespace Indexing
{

template<class LeafData_>
LiteralSubstitutionTree<LeafData_>::LiteralSubstitutionTree(Shell::Options::UnificationWithAbstraction uwa, bool useC)
: SubstitutionTree(2*env.signature->predicates(), uwa, useC)
{
  //EqualityProxy transformation can introduce polymorphism in a monomorphic problem
  //However, there is no need to guard aginst it, as equalityProxy removes all
  //equality literals. The flag below is only used during the unification of 
  //equality literals.
  _polymorphic = env.property->hasPolymorphicSym() || env.property->higherOrder();
}

template<class LeafData_>
void LiteralSubstitutionTree<LeafData_>::insert(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::insert");
  handleLiteral(lit,cls,true);
}

template<class LeafData_>
void LiteralSubstitutionTree<LeafData_>::remove(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::remove");
  handleLiteral(lit,cls,false);
}

template<class LeafData_>
void LiteralSubstitutionTree<LeafData_>::handleLiteral(Literal* lit, Clause* cls, bool insert)
{
  CALL("LiteralSubstitutionTree::handleLiteral");

  Literal* normLit=Renaming::normalize(lit);

  BindingMap svBindings;
  this->getBindings(normLit, svBindings);
  if(insert) {
    //cout << "Into " << this << " insert " << lit->toString() << endl;
    SubstitutionTree::insert(&this->_nodes[getRootNodeIndex(normLit)], svBindings, LeafData(cls, lit));
  } else {
    SubstitutionTree::remove(&this->_nodes[getRootNodeIndex(normLit)], svBindings, LeafData(cls, lit));
  }
}

template<class LeafData_>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnifications");
  if(_polymorphic){
    return getResultIterator<UnificationsIterator, UnificationFilter<true>>(lit,
  	  complementary, retrieveSubstitutions,false);
  } else {
    return getResultIterator<UnificationsIterator, UnificationFilter<false>>(lit,
      complementary, retrieveSubstitutions,false);  
  }
}
template<class LeafData_>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getUnificationsWithConstraints(Literal* lit,
          bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnificationsWithConstraints");
  if(_polymorphic){
    return getResultIterator<UnificationsIterator, UnificationFilter<true>>(lit,
      complementary, retrieveSubstitutions,true);
  } else {
    return getResultIterator<UnificationsIterator, UnificationFilter<false>>(lit,
      complementary, retrieveSubstitutions,true);
  }
}

template<class LeafData_>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getGeneralizations");

  SLQueryResultIterator res=
//  getResultIterator<GeneralizationsIterator>(lit,
    getResultIterator<FastGeneralizationsIterator, MatchingFilter<false>>(lit,
	  	  complementary, retrieveSubstitutions,false);
//  ASS_EQ(res.hasNext(), getResultIterator<GeneralizationsIterator>(lit,
//	  	  complementary, retrieveSubstitutions).hasNext());
  return res;
}

template<class LeafData_>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getInstances");

//  return getResultIterator<InstancesIterator>(lit, complementary, true);

  if(retrieveSubstitutions) {
    NOT_IMPLEMENTED;
    /*
    return getResultIterator<InstancesIterator>(lit, complementary, true, false);
    */
  }

  SLQueryResultIterator res=
//      getResultIterator<InstancesIterator>(lit,
      getResultIterator<FastInstancesIterator, MatchingFilter<true>>(lit,
	  complementary, retrieveSubstitutions, false);
//  ASS_EQ(res.hasNext(), getResultIterator<InstancesIterator>(lit,
//      complementary, retrieveSubstitutions).hasNext());
  return res;
}

template<class LeafData_>
struct LiteralSubstitutionTree<LeafData_>::SLQueryResultFunctor
{
  SLQueryResult operator() (const QueryResult& qr) {
    return SLQueryResult(qr.first.first->literal, qr.first.first->clause, qr.first.second,qr.second);
  }
};

template<class LeafData_>
struct LiteralSubstitutionTree<LeafData_>::LDToSLQueryResultFn
{
  SLQueryResult operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

template<class LeafData_>
struct LiteralSubstitutionTree<LeafData_>::LDToSLQueryResultWithSubstFn
{
  LDToSLQueryResultWithSubstFn()
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  SLQueryResult operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause,
	    ResultSubstitution::fromSubstitution(_subst.ptr(),
		    QRS_QUERY_BANK,QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

template<class LeafData_>
struct LiteralSubstitutionTree<LeafData_>::UnifyingContext
{
  UnifyingContext(Literal* queryLit)
  : _queryLit(queryLit) {}
  bool enter(SLQueryResult qr)
  {
    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);

    //This code is used only during variant retrieval, so
    //literal commutativity doesn't need to concern us, as
    //we normalize the query literal, so the argument order
    //of commutative literals is always the right one.
    ALWAYS(subst->unifyArgs(_queryLit, QRS_QUERY_BANK, qr.literal, QRS_RESULT_BANK));

    return true;
  }
  void leave(SLQueryResult qr)
  {
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);
    subst->reset();
  }
private:
  Literal* _queryLit;
};


template<class LeafData_>
struct LiteralSubstitutionTree<LeafData_>::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    return l->allChildren();
  }
};

template<class LeafData_>
struct LiteralSubstitutionTree<LeafData_>::PropositionalLDToSLQueryResultWithSubstFn
{
  PropositionalLDToSLQueryResultWithSubstFn()
  {
    _subst=ResultSubstitutionSP (new DisjunctQueryAndResultVariablesSubstitution()); 
  }
  SLQueryResult operator() (const LeafData& ld) {
    ASS_EQ(ld.literal->arity(),0);
    return SLQueryResult(ld.literal, ld.clause, _subst);
  }
private:
  ResultSubstitutionSP _subst;
};


template<class LeafData_>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");

  Node* root = this->_nodes[getRootNodeIndex(lit, complementary)];

  if(root==0) {
    return SLQueryResultIterator::getEmpty();
  }
  if(root->isLeaf()) {
    LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
    if(retrieveSubstitutions) {
      // a single substitution will be used for all in ldit, but that's OK
      return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
    } else {
      return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
    }
  }

  Literal* normLit=Renaming::normalize(lit);

  BindingMap svBindings;
  this->getBindings(normLit, svBindings);
  Leaf* leaf = this->findLeaf(root,svBindings);
  if(leaf==0) {
    return SLQueryResultIterator::getEmpty();
  }

  LDIterator ldit=leaf->allChildren();
  if(retrieveSubstitutions) {
    return pvi( getContextualIterator(
	    getMappingIterator(
		    ldit,
		    LDToSLQueryResultWithSubstFn()),
	    UnifyingContext(lit)) );
  } else {
    return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
  }
}

template<class LeafData_>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi( getMappingIterator(
      getMapAndFlattenIterator(
	  vi( new LeafIterator(this) ),
	  LeafToLDIteratorFn()),
      LDToSLQueryResultFn()) ) ;
}

// struct LiteralSubstitutionTree::EqualitySortFilter
// {
//
//   EqualitySortFilter(Literal* queryLit)
//   : _queryEqSort(SortHelper::getEqualityArgumentSort(queryLit)) {}
//
//   bool operator()(const SLQueryResult& res)
//   {
//     CALL("LiteralSubstitutionTree::EqualitySortFilter::operator()");
//     ASS(res.literal->isEquality());
//
//     unsigned resSort = SortHelper::getEqualityArgumentSort(res.literal);
//     return resSort==_queryEqSort;
//   }
// private:
//   unsigned _queryEqSort;
// };

template<class LeafData_>
template<class Iterator, class Filter>
SLQueryResultIterator LiteralSubstitutionTree<LeafData_>::getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions, bool useConstraints)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  Node* root = this->_nodes[getRootNodeIndex(lit, complementary)];

  //if(root!=0){
  //cout << "Printing root" << endl;
  //root->print(0);
  //}

  if(root==0) {
    return SLQueryResultIterator::getEmpty();
  }
  if(root->isLeaf()) {
    //cout << "Root is Leaf" << endl;
    LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
    if(retrieveSubstitutions) {
      // a single substitution will be used for all in ldit, but that's OK
      return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
    } else {
      return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
    }
  }

  if(lit->commutative()) {
    VirtualIterator<QueryResult> qrit1=vi(
  	    new Iterator(this, root, lit, retrieveSubstitutions, false, false, useConstraints) );
    VirtualIterator<QueryResult> qrit2=vi(
  	    new Iterator(this, root, lit, retrieveSubstitutions, true, false, useConstraints) );
    ASS(lit->isEquality());
    return pvi(
	getContextualIterator(
	    getMappingIterator(
		getConcatenatedIterator(qrit1,qrit2), SLQueryResultFunctor()),
	    Filter(lit, retrieveSubstitutions))
	);
  } else {
    VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
  	    new Iterator(this, root, lit, retrieveSubstitutions,false,false, useConstraints) );
    return pvi( getMappingIterator(qrit, SLQueryResultFunctor()) );
  }
}

template<class LeafData_>
unsigned LiteralSubstitutionTree<LeafData_>::getRootNodeIndex(Literal* t, bool complementary)
{
  if(complementary) {
    return t->complementaryHeader();
  } else {
    return t->header();
  }
}



}
