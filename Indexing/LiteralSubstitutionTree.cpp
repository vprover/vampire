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
#include "Kernel/UnificationWithAbstraction.hpp"
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

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return pvi(getResultIterator<SubstitutionTree::Iterator<RetrievalAlgorithms::RobUnification>>(lit, complementary, retrieveSubstitutions)); }

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return pvi(getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions)); }

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return pvi(getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions)); }


SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* query, bool complementary, bool retrieveSubstitutions)
{
  return pvi(iterTraits(getTree(query, complementary).getVariants(query, retrieveSubstitutions))
        .map([](auto qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.unif); }));
}

// TODO no substitution in this resultIterator
SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(&_trees[i]); })
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map([](auto* ld) { return SLQueryResult(ld->literal, ld->clause, ResultSubstitutionSP()); })
      );
}

} // namespace Indexing
