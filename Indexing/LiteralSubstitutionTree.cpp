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
{ }

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false); }

SLQueryResultIterator LiteralSubstitutionTree::getUnificationsWithConstraints(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<UnificationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ true); }

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false); }

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions, /* constraints */ false); }


SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* query, bool complementary, bool retrieveSubstitutions)
{
  return pvi(iterTraits(getTree(query, complementary).getVariants(query, retrieveSubstitutions))
        .map([](QueryResult qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.subst, qr.constr); }));
}

SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(&_trees[i]); })
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map([](const LeafData& ld) { return SLQueryResult(ld.literal, ld.clause); })
      );
}

SubstitutionTree& LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto idx = complementary ? lit->header() : lit->complementaryHeader();
  while (idx >= _trees.size()) {
    _trees.push(SubstitutionTree(_useC, /* rfSubs */ false));
  }
  return _trees[idx];
}

template<class Iterator>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, bool useConstraints)
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

} // namespace Indexing
