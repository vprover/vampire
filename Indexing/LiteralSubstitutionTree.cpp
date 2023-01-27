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

#include "Indexing/SubstitutionTree.hpp"
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

LiteralSubstitutionTree::LiteralSubstitutionTree(MismatchHandler* mismatchHandler)
: _trees(env.signature->predicates() * 2)
, _mismatchHandler(mismatchHandler)
{ }

void LiteralSubstitutionTree::insert(Literal* lit, Clause* cls)
{ handleLiteral(lit, cls, /* insert */ true); }

void LiteralSubstitutionTree::remove(Literal* lit, Clause* cls)
{ handleLiteral(lit, cls, /* insert */ false); }

void LiteralSubstitutionTree::handleLiteral(Literal* lit, Clause* cls, bool insert)
{ getTree(lit, /* complementary */ false).handle(lit, SubstitutionTree::LeafData(cls, lit), insert); }

// TODO move
using UwaAlgo = UnificationAlgorithms::UnificationWithAbstraction;
using RobAlgo = UnificationAlgorithms::RobUnification;

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions, bool constraints)
{ 
  return constraints ? getResultIterator<SubstitutionTree::UnificationsIterator<UwaAlgo>>(lit, complementary, retrieveSubstitutions)
                     : getResultIterator<SubstitutionTree::UnificationsIterator<RobAlgo>>(lit, complementary, retrieveSubstitutions); 
}

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions); }

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions); }


SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* query, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");

  auto& tree = getTree(query, complementary);
  return pvi(iterTraits(tree.getVariants(query, retrieveSubstitutions))
        .map([](auto qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.unif); }));
}

SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(&*_trees[i]); })
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map([](const LeafData& ld) { return SLQueryResult(ld.literal, ld.clause); })
      );
}

SubstitutionTree& LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto idx = complementary ? lit->header() : lit->complementaryHeader();
  while (idx >= _trees.size()) {
    _trees.push(make_unique<SubstitutionTree>());
  }
  return *_trees[idx];
}
template<class Unifier>
SLQueryResult createSLQueryResult(SubstitutionTree::QueryResult<Unifier> r);

SLQueryResult createSLQueryResult(SubstitutionTree::QueryResult<ResultSubstitutionSP> r)
{ return SLQueryResult(r.data->literal, r.data->clause, r.unif, nullptr); }

SLQueryResult createSLQueryResult(SubstitutionTree::QueryResult<Option<ResultSubstitutionSP>> r)
{ return SLQueryResult(r.data->literal, r.data->clause, r.unif.unwrapOrElse([](){return ResultSubstitutionSP();}), nullptr); }

SLQueryResult createSLQueryResult(SubstitutionTree::QueryResult<Option<RobSubstitutionSP>> r)
{ return SLQueryResult(r.data->literal, r.data->clause, ResultSubstitutionSP((ResultSubstitution*)&*r.unif.unwrapOrElse([](){return RobSubstitutionSP();})), nullptr); }

template<class Iterator, class... Args>
SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, Args... args)
{
  CALL("LiteralSubstitutionTree::getResultIterator");

  auto iter = [&](bool reversed) 
    { return iterTraits(getTree(lit, complementary).iterator<Iterator>(lit, retrieveSubstitutions, reversed, args...)) ; };

  auto filterResults = [=](auto it) { 
    return pvi(
        std::move(it)
        .map([](auto qr) { return createSLQueryResult(std::move(qr)); })
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
