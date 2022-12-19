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
: _useC(useC)
, _trees(env.signature->predicates() * 2)
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
  auto& tree = getTree(lit, /* complementary */ false);

  BindingMap svBindings;
  SubstitutionTree::createInitialBindings(normLit, /* reversed */ false, /* withoutTop */ false, 
      [&](auto var, auto term) { 
        svBindings.insert(var, term);
        tree._nextVar = max(tree._nextVar, (int)var + 1);
      });

  tree.handle(svBindings, SubstitutionTree::LeafData(cls, lit), insert);
}

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnifications");
  // TODO write non-polymorphic optimization
  return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false);
}
SLQueryResultIterator LiteralSubstitutionTree::getUnificationsWithConstraints(Literal* lit, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getUnificationsWithConstraints");
  // if(_polymorphic){
  return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ true);
  // }
}

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getGeneralizations");

  // TODO write non-polymorphic optimization
  return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false);
}

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit,
	  bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getInstances");
  return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false);
}

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


SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* lit, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");


  auto& tree = getTree(lit, complementary);
  // // TODO get rid of the explicit access of private member _root
  // auto root = tree._root;
  //
  // if(root==0) {
  //   return SLQueryResultIterator::getEmpty();
  // }
  // if(root->isLeaf()) {
  //   LDIterator ldit=static_cast<Leaf*>(root)->allChildren();
  //   if(retrieveSubstitutions) {
  //     // a single substitution will be used for all in ldit, but that's OK
  //     return pvi( getMappingIterator(ldit,PropositionalLDToSLQueryResultWithSubstFn()) );
  //   } else {
  //     return pvi( getMappingIterator(ldit,LDToSLQueryResultFn()) );
  //   }
  // }

  Literal* normLit=Renaming::normalize(lit);

  BindingMap svBindings;
  SubstitutionTree::createInitialBindings(normLit, /* reversed */ false, /* withoutTop */ false, 
      [&](auto v, auto t) { {
        tree._nextVar = max<int>(tree._nextVar, v + 1);
        svBindings.insert(v, t);
      } });
  Leaf* leaf = tree.findLeaf(svBindings);
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

  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(&*_trees[i]); })
        // iterTraits(LeafIterator(&tree))
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map(LDToSLQueryResultFn())
      );
}

SubstitutionTree& LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto idx = complementary ? lit->header() : lit->complementaryHeader();
  while (idx >= _trees.size()) {
    _trees.push(make_unique<SubstitutionTree>(_useC));
  }
  return *_trees[idx];
}

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, bool useConstraints)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  // auto& tree = getTree(lit, complementary);
  auto iter = [&](bool reversed) 
    { return iterTraits(getTree(lit, complementary).iterator<Iterator>(lit, retrieveSubstitutions, useConstraints, /* funcSubtermMap */ nullptr, reversed)) ; };

  auto filterResults = [=](auto it) { 
    return pvi(
        std::move(it)
        // .filter([=](auto& qr) { return complementary ? qr.data->literal->polarity() != lit->polarity() 
        //                                              : qr.data->literal->polarity() == lit->polarity(); })
        .map([](QueryResult qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.subst,qr.constr); })
        ); 
  };
  return !lit->commutative() 
    ?  filterResults(iter( /* reversed */ false))
    :  filterResults(concatIters(
        iter( /* reversed */ false),
        iter( /* reversed */ true)
      ));
}

} // namespace Indexing
