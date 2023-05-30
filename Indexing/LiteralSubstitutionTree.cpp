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
#include "Indexing/HOLSubstitutionTree.hpp"
#include "Kernel/MismatchHandler.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"

#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Statistics.hpp"

#include "LiteralSubstitutionTree.hpp"

namespace Indexing
{

LiteralSubstitutionTree::LiteralSubstitutionTree(SplittingAlgo algo)
: _algo(algo), _trees(env.signature->predicates() * 2)
{ }

SLQueryResultIterator LiteralSubstitutionTree::getUnifications(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<SubstitutionTree::TreeIterator<RobAlgo>>(lit, complementary, retrieveSubstitutions); }

SLQueryResultIterator LiteralSubstitutionTree::getGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastGeneralizationsIterator>(lit, complementary, retrieveSubstitutions); }

SLQueryResultIterator LiteralSubstitutionTree::getInstances(Literal* lit, bool complementary, bool retrieveSubstitutions)
{ return getResultIterator<FastInstancesIterator>(lit, complementary, retrieveSubstitutions); }

#if VHOL
  SLQueryResultIterator LiteralSubstitutionTree::getHOLInstances(Literal* lit, bool complementary, bool retrieveSubstitutions)
  { return getResultIterator<SubstitutionTree::TreeIterator<HOLInstAlgo>>(lit, complementary, retrieveSubstitutions);  }

  SLQueryResultIterator LiteralSubstitutionTree::getHOLGeneralizations(Literal* lit, bool complementary, bool retrieveSubstitutions)
  { return getResultIterator<SubstitutionTree::TreeIterator<HOLGenAlgo>>(lit, complementary, retrieveSubstitutions);  }
#endif

SLQueryResultIterator LiteralSubstitutionTree::getVariants(Literal* query, bool complementary, bool retrieveSubstitutions)
{
  CALL("LiteralSubstitutionTree::getVariants");

  return pvi(iterTraits(getTree(query, complementary)->getVariants(query, retrieveSubstitutions))
        .map([](auto qr) { return SLQueryResult(qr.data->literal, qr.data->clause, qr.unif); }));
}

// TODO no substitution in this resultIterator
SLQueryResultIterator LiteralSubstitutionTree::getAll()
{
  CALL("LiteralSubstitutionTree::getAll");

  return pvi(
        iterTraits(getRangeIterator((unsigned long)0, _trees.size()))
         .flatMap([this](auto i) { return LeafIterator(_trees[i]); })
         .flatMap([](Leaf* l) { return l->allChildren(); })
         .map([](auto ld) { return SLQueryResult(ld->literal, ld->clause, ResultSubstitutionSP()); })
      );
}

SubstitutionTree* LiteralSubstitutionTree::getTree(Literal* lit, bool complementary)
{
  auto idx = complementary ? lit->header() : lit->complementaryHeader();
  while (idx >= _trees.size()) {
    switch(_algo){
      case SplittingAlgo::NONE:
        _trees.push(new SubstitutionTree());
        break;
  #if VHOL
      case SplittingAlgo::HOL_UNIF:
        ASSERTION_VIOLATION; // currently we don't expect any literal index to use higher-order unif
        break;
      case SplittingAlgo::HOL_MATCH:
        _trees.push(new HOLSubstitutionTree([](TermList t){     
            return !t.isLambdaTerm();
          } ));
        break;      
  #endif
    }    
  }
  return _trees[idx];
}

// template<class Iterator, class... Args>
// SLQueryResultIterator LiteralSubstitutionTree::getResultIterator(Literal* lit, bool complementary, bool retrieveSubstitutions, Args... args)


} // namespace Indexing
