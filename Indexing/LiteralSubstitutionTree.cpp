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

#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Shell/Statistics.hpp"

#include "LiteralSubstitutionTree.hpp"

namespace Indexing
{

LiteralSubstitutionTree::LiteralSubstitutionTree(bool useC)
: _trees(env.signature->predicates() * 2)
, _useC(useC)
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
  // TODO make this and insnert one fuction

  Literal* normLit=Renaming::normalize(lit);

  BindingMap svBindings;
  auto& tree = getTree(lit);
  int var = 0;
  for (auto a : anyArgIter(normLit)) {
    svBindings.insert(var++, a);
  }
  tree._nextVar = max(tree._nextVar, var);

  if(insert) {
    tree.insert(svBindings, SubstitutionTree::LeafData(cls, lit));
  } else {
    tree.remove(svBindings, SubstitutionTree::LeafData(cls, lit));
  }
}

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit,
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
SLQueryResultIterator LiteralSubstitutionTree::getUnificationsWithConstraints(Literal* lit,
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

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit,
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

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit,
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

struct LiteralSubstitutionTree::LDToSLQueryResultWithSubstFn
{
  LDToSLQueryResultWithSubstFn()
  {
    _subst=RobSubstitutionSP(new RobSubstitution());
  }
  SLQueryResult operator() (const LeafData& ld) {
    return SLQueryResult(ld.literal, ld.clause,
	    ResultSubstitution::fromSubstitution(_subst.ptr(),
		    SubstitutionTree::QRS_QUERY_BANK,SubstitutionTree::QRS_RESULT_BANK));
  }
private:
  RobSubstitutionSP _subst;
};

struct LiteralSubstitutionTree::UnifyingContext
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
    ALWAYS(subst->unifyArgs(_queryLit, SubstitutionTree::QRS_QUERY_BANK, qr.literal, SubstitutionTree::QRS_RESULT_BANK));

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


SubstitutionTree& LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto getPos = lit->isPositive() != complementary;
  auto idx = lit->functor() * 2 + (getPos ? 1 : 0);
  while (idx >= _trees.size()) {
    _trees.push(make_unique<SubstitutionTree>(_useC));
  }
  return *_trees[idx];
}

SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");


  auto& tree = getTree(lit, complementary);
  // TODO get rid of the explicit access of private member _root
  auto root = tree._root;

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
  SubstitutionTree::createIteratorBindings(normLit, /* reversed */ false, /* withoutTop */ false, 
      [&](auto v, auto t) { {
        tree._nextVar = max<int>(tree._nextVar, v + 1);
        svBindings.insert(v, t);
      } });
  Leaf* leaf=tree.findLeaf(root,svBindings);
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

SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi( getMappingIterator(
      getMapAndFlattenIterator(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return vi(new LeafIterator(&*_trees[i])); })
        ,
        [](Leaf* l) { return l->allChildren(); }),
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
	  bool complementary, bool retrieveSubstitutions, bool useConstraints)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  auto& tree = getTree(lit, complementary);
  auto root = tree._root;

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
  	    new Iterator(&tree, root, lit, retrieveSubstitutions, false, false, useConstraints) );
    VirtualIterator<QueryResult> qrit2=vi(
  	    new Iterator(&tree, root, lit, retrieveSubstitutions, true, false, useConstraints) );
    ASS(lit->isEquality());
    return pvi(
	getContextualIterator(
	    getMappingIterator(
		getConcatenatedIterator(qrit1,qrit2), SLQueryResultFunctor()),
	    Filter(lit, retrieveSubstitutions))
	);
  } else {
    VirtualIterator<QueryResult> qrit=VirtualIterator<QueryResult>(
  	    new Iterator(&tree, root, lit, retrieveSubstitutions,false,false, useConstraints) );
    return pvi( getMappingIterator(qrit, SLQueryResultFunctor()) );
  }
}

}
