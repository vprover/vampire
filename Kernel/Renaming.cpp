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
 * @file Renaming.cpp
 * Implements class Renaming
 */

#include "Debug/RuntimeStatistics.hpp"

#include "Lib/DArray.hpp"
#include "Indexing/TermSharing.hpp"

#include "SubstHelper.hpp"
#include "TermIterators.hpp"

#include "Renaming.hpp"

#if VDEBUG
#include "Lib/Int.hpp"
#include "Lib/Set.hpp"
#endif

namespace Kernel {

using namespace Lib;
using namespace Indexing;

Literal* Renaming::apply(Literal* lit)
{
  CALL("Renaming::apply(Literal*...)");

  if((identity() && _bank == DEFAULT_BANK) || 
     (lit->shared()  && lit->ground())) {
    return lit;
  }
  Applicator a(this);
  return SubstHelper::apply(lit, a);
}

Term* Renaming::apply(Term* trm)
{
  CALL("Renaming::apply(Term*...)");

  if((identity() && _bank == DEFAULT_BANK) || 
     (trm->shared()  && trm->ground())) {
    return trm;
  }
  Applicator a(this);
  return SubstHelper::apply(trm, a);
}

TermList Renaming::apply(TermList trm)
{
  CALL("Renaming::apply(TermList...)");

  if((identity() && _bank == DEFAULT_BANK) || 
     (trm.isTerm() && trm.term()->shared() && trm.term()->ground())) {   
    return trm;
  }
  Applicator a(this);
  return SubstHelper::apply(trm, a);
}

bool Renaming::identity() const
{
#if VDEBUG
  VariableMap::Iterator mit(_data);
  bool shouldBeIdentity = true;
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    if(from!=to) {
      shouldBeIdentity = false;
    }
  }
//  ASS_EQ(_identity, shouldBeIdentity);
#endif
  return _identity;
}

/**
 * Make the renaming normalize variables of term or literal @c t
 */
void Renaming::normalizeVariables(const Term* t)
{
  static VariableIterator vit;
  vit.reset(t);
  while(vit.hasNext()) {
    TermList var=vit.next();
    if(var.isOrdinaryVar()) {
      getOrBind(var.var(), var.bank());
    }
  }
}

void Renaming::normalizeVariables(TermList t)
{
  if(t.isOrdinaryVar()) {
    getOrBind(t.var(), t.bank());
  } else if(t.isTerm()) {
    normalizeVariables(t.term());
  }
}

void Renaming::makeInverse(const Renaming& orig)
{
  ASS_EQ(_nextVar,0);
  VariableMap::Iterator mit(orig._data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    ALWAYS(_data.set(to,from));
    if(_nextVar<=from) {
      _nextVar=from+1;
    }
  }
  _identity = orig.identity();
}

TypedTermList Renaming::normalize(TypedTermList l, VarBank bank)
{
  CALL("Renaming::normalize(Literal*)");
  if (l.isTerm()) {
    return TypedTermList(normalize(l.term(), bank));
  } else {
    Recycled<Renaming> n(0, bank);
    n->normalizeVariables(TermList(l));
    n->normalizeVariables(l.sort());
    return TypedTermList(n->apply(TermList(l)), n->apply(l.sort()));
  }
}


Literal* Renaming::normalize(Literal* l, VarBank bank)
{
  CALL("Renaming::normalize(Literal*)");

  Recycled<Renaming> n(0, bank);
  n->normalizeVariables(l);
  return n->apply(l);
}

Term* Renaming::normalize(Term* trm, VarBank bank)
{
  CALL("Renaming::normalize(Term*)");

  Recycled<Renaming> n(0, bank);
  n->normalizeVariables(trm);
  return n->apply(trm);
}

TermList Renaming::normalize(TermList trm, VarBank bank)
{
  CALL("Renaming::normalize(TermList)");

  Recycled<Renaming> n(0, bank);
  n->normalizeVariables(trm);
  return n->apply(trm);
}


#if VDEBUG

void Renaming::assertValid() const
{
  Set<unsigned> range;
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned to = mit.next();
    ASS(!range.contains(to));
    range.insert(to);
  }
}

vstring Renaming::toString() const
{
  vstring res = "[";
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    res+=Int::toString(from)+" -> "+Int::toString(to)+"\t";
  }
  return res+"]";
}

#endif

}
