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
 * @file TermSubstitutionTree.cpp
 * Implements class TermSubstitutionTree.
 */

#include "Lib/Environment.hpp"
#include "Lib/Metaiterators.hpp"
#include "Lib/Random.hpp"
#include "Lib/SmartPtr.hpp"

#include "Kernel/TermIterators.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/ApplicativeHelper.hpp"

#include "Shell/Options.hpp"

#include "TermSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TermSubstitutionTree::TermSubstitutionTree(bool useC, bool rfSubs, bool extra)
: SubstitutionTree(useC, rfSubs)
, _extra(extra)
, _extByAbs(rfSubs)
{ }

void TermSubstitutionTree::insert(TermList t, TermList trm)
{ handleTerm(t, LeafData(0, 0, t, trm), /* insert */ true); }

void TermSubstitutionTree::insert(TermList t, TermList trm, Literal* lit, Clause* cls)
{ handleTerm(t, LeafData(cls, lit, t, trm), /* insert */ true); }

void TermSubstitutionTree::insert(TermList t, Literal* lit, Clause* cls)
{ handleTerm(t, LeafData(cls,lit,t), /* insert */ true); }

void TermSubstitutionTree::handle(TypedTermList tt, Literal* lit, Clause* cls, bool insert)
{ handleTerm(tt, LeafData(cls,lit,tt), insert); }

void TermSubstitutionTree::remove(TermList t, Literal* lit, Clause* cls)
{ handleTerm(t, LeafData(cls,lit,t), /* insert */ false); }

/**
 * According to value of @b insert, insert or remove term.
 */
template<class TypedOrUntypedTermList>
void TermSubstitutionTree::handleTerm(TypedOrUntypedTermList tt, LeafData ld, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");
  SubstitutionTree::handle(tt, ld, insert, _extByAbs ? &_functionalSubtermMap : nullptr);
}

TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t, bool retrieveSubstitutions, bool withConstraints)
{
  CALL("TermSubstitutionTree::getUnifications");
  return pvi(getResultIterator<UnificationsIterator>(t, retrieveSubstitutions, withConstraints));
}

//higher-order concern
TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions, bool withConstr)
{
  CALL("TermSubstitutionTree::getUnificationsUsingSorts");
  return pvi(getResultIterator<UnificationsIterator>(tt, retrieveSubstitutions, withConstr));
}


bool TermSubstitutionTree::generalizationExists(TermList t)
{
  return t.isVar() ? false
                   : SubstitutionTree::generalizationExists(t);
}

/**
 * Return iterator, that yields generalizations of the given term.
 */
TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions, /* constraints */ false));
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions, /* constraints */ false));
}

} // namespace  Indexing
