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

#include "Forwards.hpp"
#include "Indexing/SubstitutionTree.hpp"
#include "Kernel/MismatchHandler.hpp"
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

LiteralSubstitutionTree::LiteralSubstitutionTree()
: _trees(env.signature->predicates() * 2)
{ }

// TODO move
using UwaAlgo = UnificationAlgorithms::UnificationWithAbstraction;
using RobAlgo = UnificationAlgorithms::RobUnification;

VirtualIterator<LQueryRes<RobSubstitution*>> LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<SubstitutionTree::UnificationsIterator<RobAlgo>>(lit, complementary, retrieveSubstitutions); }

VirtualIterator<LQueryRes<SmartPtr<GenSubstitution>>> LiteralSubstitutionTree::getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions); }

VirtualIterator<LQueryRes<SmartPtr<InstSubstitution>>> LiteralSubstitutionTree::getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions); }


VirtualIterator<LQueryRes<SmartPtr<ResultSubstitution>>> LiteralSubstitutionTree::getVariants(Literal* query, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");

  return pvi(iterTraits(getTree(query, complementary).getVariants(query, retrieveSubstitutions))
        .map([](auto qr) { return lQueryRes(qr.data->literal, qr.data->clause, qr.unif); }));
}

// TODO no substitution in this resultIterator
VirtualIterator<LQueryRes<Nothing>> LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(&_trees[i]); })
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map([](auto ld) { return lQueryRes(ld->literal, ld->clause, Nothing()); })
      );
}

SubstitutionTree& LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto idx = complementary ? lit->header() : lit->complementaryHeader();
  while (idx >= _trees.size()) {
    _trees.push(SubstitutionTree());
  }
  return _trees[idx];
}

} // namespace Indexing
