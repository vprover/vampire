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

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/TimeCounter.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"

#include "Shell/Statistics.hpp"

#include "LiteralSubstitutionTree.hpp"

namespace Indexing
{

LiteralSubstitutionTree::LiteralSubstitutionTree(MismatchHandler const& handler)
  : SubstitutionTree(2*env.signature->predicates(), handler)
{
  //EqualityProxy transformation can introduce polymorphism in a monomorphic problem
  //However, there is no need to guard aginst it, as equalityProxy removes all
  //equality literals. The flag below is only used during the unification of 
  //equality literals.
  _polymorphic = env.property->hasPolymorphicSym() || env.property->higherOrder();
}

void LiteralSubstitutionTree::insert(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::insert");
  handleLiteral(lit,cls,true);
}

void LiteralSubstitutionTree::remove(Literal* lit, Clause* cls)
{
  CALL("LiteralSubstitutionTree::remove");
  handleLiteral(lit,cls,false);
}

void LiteralSubstitutionTree::handleLiteral(Literal* lit, Clause* cls, bool insert)
{
  CALL("LiteralSubstitutionTree::handleLiteral");

  Literal* normLit=Renaming::normalize(lit);

  if(!_handler.isEmpty()){
    // TODO why not equality ?!
    ASS(!lit->isEquality());
    // replace theory subterms by very special variables
    // For example f($sum(X,Y), b)   ---> f(#, b)
    TheoryTermReplacement ttr(&_termMap, _handler);
    normLit = ttr.transform(normLit);
  }

  BindingMap svBindings;
  getBindings(normLit, svBindings);
  if(insert) {
    //cout << "Into " << this << " insert " << lit->toString() << endl;
    SubstitutionTree::insert(&_nodes[getRootNodeIndex(normLit)], svBindings, LeafData(cls, lit));
  } else {
    SubstitutionTree::remove(&_nodes[getRootNodeIndex(normLit)], svBindings, LeafData(cls, lit));
  }
}

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnifications");
  if(_polymorphic){
    return getResultIterator<UnificationsIterator, UnificationFilter<true>>(lit,
  	  complementary, retrieveSubstitutions);
  } else {
    return getResultIterator<UnificationsIterator, UnificationFilter<false>>(lit,
      complementary, retrieveSubstitutions);  
  }
}

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getGeneralizations");

  SLQueryResultIterator res=
//  getResultIterator<GeneralizationsIterator>(lit,
    getResultIterator<FastGeneralizationsIterator, MatchingFilter<false>>(lit,
	  	  complementary, retrieveSubstitutions);
//  ASS_EQ(res.hasNext(), getResultIterator<GeneralizationsIterator>(lit,
//	  	  complementary, retrieveSubstitutions).hasNext());
  return res;
}

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getInstances");


  if(retrieveSubstitutions) {
    NOT_IMPLEMENTED;
    /*
    return getResultIterator<InstancesIterator>(lit, complementary, true, false);
    */
  }

  SLQueryResultIterator res=
      getResultIterator<FastInstancesIterator, MatchingFilter<true>>(lit,
	  complementary, retrieveSubstitutions);

  return res;
}

struct LiteralSubstitutionTree::SLQueryResultFunctor
{
  SLQueryResult operator() (const QueryResult& qr) {
    return SLQueryResult(qr.first.first->literal, qr.first.first->clause, qr.first.second,qr.second);
  }
};

struct LiteralSubstitutionTree::LDToSLQueryResultFn
{
  SLQueryResult operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause);
  }
};

#define QRS_QUERY_BANK 0
#define QRS_RESULT_BANK 1

struct LiteralSubstitutionTree::LDToSLQueryResultWithSubstFn
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

struct LiteralSubstitutionTree::UnifyingContext
{
  UnifyingContext(Literal* queryLit, MismatchHandler const& handler)
    : _queryLit(queryLit) 
    , _handler(handler)
  {}
  bool enter(SLQueryResult qr)
  {
    ASS(qr.substitution);
    RobSubstitution* subst=qr.substitution->tryGetRobSubstitution();
    ASS(subst);

    //This code is used only during variant retrieval, so
    //literal commutativity doesn't need to concern us, as
    //we normalize the query literal, so the argument order
    //of commutative literals is always the right one.
    ALWAYS(subst->unifyArgs(_queryLit, QRS_QUERY_BANK, qr.literal, QRS_RESULT_BANK, _handler, *qr.constraints));

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
  MismatchHandler const& _handler;
};


struct LiteralSubstitutionTree::LeafToLDIteratorFn
{
  LDIterator operator() (Leaf* l) {
    return l->allChildren();
  }
};

struct LiteralSubstitutionTree::PropositionalLDToSLQueryResultWithSubstFn
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


// SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* lit,
// 	  bool complementary, bool retrieveSubstitutions)
// {
//   CALL("LiteralSubstitutionTree::getVariants");
//
//   Node* root=_nodes[getRootNodeIndex(lit, complementary)];
//
//   if(root==0) {
//     return SLQueryResultIterator::getEmpty();
//   }
//   if(root->isLeaf()) {
//     LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
//     if(retrieveSubstitutions) {
//       // a single substitution will be used for all in ldit, but that's OK
//       return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
//     } else {
//       return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
//     }
//   }
//
//   Literal* normLit=Renaming::normalize(lit);
//
//   BindingMap svBindings;
//   getBindings(normLit, svBindings);
//   Leaf* leaf=findLeaf(root,svBindings);
//   if(leaf==0) {
//     return SLQueryResultIterator::getEmpty();
//   }
//
//   LDIterator ldit=leaf->allChildren();
//   if(retrieveSubstitutions) {
//     return pvi( getContextualIterator(
// 	    getMappingIterator(
// 		    ldit,
// 		    LDToSLQueryResultWithSubstFn()),
// 	    UnifyingContext(lit)) );
//   } else {
//     return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
//   }
// }

SLQueryResultIterator LiteralSubstitutionTree::getAll()
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

template<class Iterator, class Filter>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  Node* root=_nodes[getRootNodeIndex(lit, complementary)];

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
    // Amongst inferences that require literal unification, constraints are only used for
    // binary resolution which does not involve equality
    VirtualIterator<QueryResult> qrit1=vi(
  	    new Iterator(this, root, lit, retrieveSubstitutions, false, false, &_termMap, _handler) );
    VirtualIterator<QueryResult> qrit2=vi(
  	    new Iterator(this, root, lit, retrieveSubstitutions, true, false, &_termMap, _handler) );
    ASS(lit->isEquality());
    return pvi(
	getContextualIterator(
	    getMappingIterator(
		getConcatenatedIterator(qrit1,qrit2), SLQueryResultFunctor()),
	    Filter(lit, retrieveSubstitutions, _handler))
	);
  } else {
    VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
  	    new Iterator(this, root, lit, retrieveSubstitutions,false,false, &_termMap, _handler) );
    return pvi( getMappingIterator(qrit, SLQueryResultFunctor()) );
  }
}

unsigned LiteralSubstitutionTree::getRootNodeIndex(Literal* t, bool complementary)
{
  if(complementary) {
    return t->complementaryHeader();
  } else {
    return t->header();
  }
}



}
