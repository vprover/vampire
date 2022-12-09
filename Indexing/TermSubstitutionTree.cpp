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
: SubstitutionTree(useC, rfSubs), _extByAbs(rfSubs)
{
  _extra = extra;
}

TypedTermList toTyped(TermList t) 
{ return t.isTerm() ? TypedTermList(t.term())
                    : TypedTermList(t, TermList::var(t.var() + 1)); }

void TermSubstitutionTree::insert(TermList t, TermList trm)
{ handleTerm(toTyped(t), LeafData(0, 0, toTyped(t), trm), /* insert */ true); }

void TermSubstitutionTree::insert(TermList t, TermList trm, Literal* lit, Clause* cls)
{ handleTerm(toTyped(t), LeafData(cls, lit, toTyped(t), trm), /* insert */ true); }

void TermSubstitutionTree::insert(TermList t, Literal* lit, Clause* cls)
{ handleTerm(toTyped(t), LeafData(cls,lit,toTyped(t)), /* insert */ true); }

void TermSubstitutionTree::handle(TypedTermList tt, Literal* lit, Clause* cls, bool insert)
{ handleTerm(tt, LeafData(cls,lit,tt), insert); }

void TermSubstitutionTree::remove(TermList t, Literal* lit, Clause* cls)
{ handleTerm(toTyped(t), LeafData(cls,lit,toTyped(t)), /* insert */ false); }

TypedTermList normalizeRenaming(TypedTermList t) 
{
  Renaming n;
  n.normalizeVariables(t);
  n.normalizeVariables(t.sort());
  return TypedTermList(n.apply(t), n.apply(t.sort()));
}

/**
 * According to value of @b insert, insert or remove term.
 */
void TermSubstitutionTree::handleTerm(TypedTermList tt, LeafData ld, bool insert)
{
  CALL("TermSubstitutionTree::handleTerm");
  auto normTerm = normalizeRenaming(tt);

  if(_extByAbs){
    normTerm = ApplicativeHelper::replaceFunctionalAndBooleanSubterms(normTerm, &_functionalSubtermMap);   
  }

  BindingMap svBindings;


  SubstitutionTree::createInitialBindings(normTerm, /* reversed */ false, /* withoutTop */ false, 
      [&](auto var, auto term) { 
        svBindings.insert(var, term);
        _nextVar = max(_nextVar, (int)var + 1);
      });

  if(insert) {
    SubstitutionTree::insert(svBindings, ld);
  } else {
    SubstitutionTree::remove(svBindings, ld);
  }
}

TermQueryResultIterator TermSubstitutionTree::getUnifications(TermList t, bool retrieveSubstitutions, bool withConstraints)
{
  CALL("TermSubstitutionTree::getUnifications");
  return getResultIterator<UnificationsIterator>(toTyped(t), retrieveSubstitutions, withConstraints);
}

//higher-order concern
TermQueryResultIterator TermSubstitutionTree::getUnificationsUsingSorts(TypedTermList tt, bool retrieveSubstitutions, bool withConstr)
{
  CALL("TermSubstitutionTree::getUnificationsUsingSorts");
  return getResultIterator<UnificationsIterator>(tt, retrieveSubstitutions, withConstr);
}


bool TermSubstitutionTree::generalizationExists(TermList t)
{
  if(!t.isTerm()) {
    return false;
  }
  if(!_root) {
    return false;
  }
  if(_root->isLeaf()) {
    return true;
  }
  return FastGeneralizationsIterator(this, _root, toTyped(t), false,false,false, /* useC */ false).hasNext();
}

/**
 * Return iterator, that yields generalizations of the given term.
 */
TermQueryResultIterator TermSubstitutionTree::getGeneralizations(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getGeneralizations");
  return getResultIterator<FastGeneralizationsIterator>(toTyped(t), retrieveSubstitutions,false);
}

TermQueryResultIterator TermSubstitutionTree::getInstances(TermList t, bool retrieveSubstitutions)
{
  CALL("TermSubstitutionTree::getInstances");
  return getResultIterator<FastInstancesIterator>(toTyped(t), retrieveSubstitutions,false);
}

// TODO get rid of this method
template<class Iterator>
TermQueryResultIterator TermSubstitutionTree::getResultIterator(TypedTermList trm, bool retrieveSubstitutions,bool withConstraints)
{ return SubstitutionTree::iterator<Iterator>(trm, retrieveSubstitutions, withConstraints, _extra, (_extByAbs ? &_functionalSubtermMap : nullptr)); }

}
