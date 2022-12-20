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
#include "Kernel/Term.hpp"
#include "TermSubstitutionTree.hpp"

namespace Indexing
{

using namespace Lib;
using namespace Kernel;

TermSubstitutionTree::TermSubstitutionTree(bool useC, bool rfSubs, bool extra)
: SubstitutionTree(useC, /* polymorphic */ env.property->hasPolymorphicSym() || env.property->higherOrder(), rfSubs)
, _extra(extra)
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
{ SubstitutionTree::handle(tt, ld, insert); }

TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t, bool retrieveSubstitutions, bool withConstraints)
{ return pvi(getResultIterator<UnificationsIterator>(t, retrieveSubstitutions, withConstraints)); }

TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions, bool withConstr)
{ return pvi(getResultIterator<UnificationsIterator>(tt, retrieveSubstitutions, withConstr)); }

bool TermSubstitutionTree::generalizationExists(TermList t)
{ return t.isVar() ? false : SubstitutionTree::generalizationExists(t); }

/**
 * Return iterator, that yields generalizations of the given term.
 */
TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t, bool retrieveSubstitutions)
{ return pvi(getResultIterator<FastGeneralizationsIterator>(t, retrieveSubstitutions, /* constraints */ false)); }

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t, bool retrieveSubstitutions)
{ return pvi(getResultIterator<FastInstancesIterator>(t, retrieveSubstitutions, /* constraints */ false)); }

} // namespace  Indexing
