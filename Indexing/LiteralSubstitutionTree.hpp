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
 * @file LiteralSubstitutionTree.hpp
 * Defines class LiteralSubstitutionTree.
 */


#ifndef __LiteralSubstitutionTree__
#define __LiteralSubstitutionTree__

#include "Indexing/Index.hpp"
#include "LiteralIndexingStructure.hpp"
#include "SubstitutionTree.hpp"

namespace Indexing {

/** A wrapper class around SubstitutionTree that makes it usable  as a LiteralIndexingStructure */
template<class LeafData_ = DefaultLiteralLeafData>
class LiteralSubstitutionTree
: public LiteralIndexingStructure
{
  using SubstitutionTree = Indexing::SubstitutionTree<LeafData_>;
  using LeafData         = LeafData_;
  using BindingMap                  = typename SubstitutionTree::BindingMap;
  using Node                        = typename SubstitutionTree::Node;
  using FastInstancesIterator       = typename SubstitutionTree::FastInstancesIterator;
  using FastGeneralizationsIterator = typename SubstitutionTree::FastGeneralizationsIterator;
  using UnificationsIterator        = typename SubstitutionTree::UnificationsIterator;
  using QueryResult                 = typename SubstitutionTree::QueryResult;
  using LDIterator                  = typename SubstitutionTree::LDIterator;
  using Leaf                        = typename SubstitutionTree::Leaf;
  using LeafIterator                = typename SubstitutionTree::LeafIterator;

public:
  CLASS_NAME(LiteralSubstitutionTree);
  USE_ALLOCATOR(LiteralSubstitutionTree);

  LiteralSubstitutionTree(bool useC=false)
    : _trees(env.signature->predicates() * 2)
    , _useC(useC)
    { }

  void handle(Literal* lit, Clause* cls, bool insert) final override
  { getTree(lit, /* complementary */ false).handle(LeafData(cls, lit), insert); }

  SLQueryResultIterator getAll() final override
  {
    CALL("LiteralSubstitutionTree::getAll");

    return pvi(
          iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
           .flatMap([this](auto i) { return LeafIterator(&_trees[i]); })
           .flatMap([](Leaf* l) { return l->allChildren(); })
           .map([](const LeafData& ld) { return SLQueryResult(ld.literal, ld.clause); })
        );
  }

  SLQueryResultIterator getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false); }

  SLQueryResultIterator getUnificationsWithConstraints(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ true); }

  SLQueryResultIterator getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false); }

  SLQueryResultIterator getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions) final override
  { return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false); }

  SLQueryResultIterator getVariants(Literal* query, bool complementary, bool retrieveSubstitutions) final override
  {
    return pvi(iterTraits(getTree(query, complementary).getVariants(query, retrieveSubstitutions))
          .map([](QueryResult qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.subst, qr.constr); }));
  }


private:
  SubstitutionTree& getTree(Literal* lit, bool complementary)
  {
    auto idx = complementary ? lit->header() : lit->complementaryHeader();
    while (idx >= _trees.size()) {
      _trees.push(SubstitutionTree(_useC, /* rfSubs */ false));
    }
    return _trees[idx];
  }

  template<class Iterator>
  SLQueryResultIterator getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, bool useConstraints)
  {
    CALL("LiteralSubstitutionTree::getResultIterator");

    auto iter = [&](bool reversed) 
      { return iterTraits(getTree(lit, complementary).iterator<Iterator>(lit, retrieveSubstitutions, useConstraints, reversed)) ; };

    auto filterResults = [=](auto it) { 
      return pvi(
          std::move(it)
          .map([](QueryResult qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.subst, qr.constr); })
          ); 
    };
    return !lit->commutative() 
      ?  filterResults(iter( /* reversed */ false))
      :  filterResults(concatIters(
          iter( /* reversed */ false),
          iter( /* reversed */ true)
        ));
  }

  Stack<SubstitutionTree> _trees;
  bool _useC;
};

};

#endif /* __LiteralSubstitutionTree__ */
