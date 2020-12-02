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

  if(identity()) {
    return lit;
  }
  Applicator a(this);
  return SubstHelper::apply(lit, a);
}

Term* Renaming::apply(Term* trm)
{
  CALL("Renaming::apply(Term*...)");

  if(identity()) {
    return trm;
  }
  Applicator a(this);
  return SubstHelper::apply(trm, a);
}

TermList Renaming::apply(TermList trm)
{
  CALL("Renaming::apply(TermList...)");

  if(identity()) {
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
  ASS_EQ(_identity, shouldBeIdentity);
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
      getOrBind(var.var());
    }
  }
}

void Renaming::normalizeVariables(TermList t)
{
  if(t.isOrdinaryVar()) {
    getOrBind(t.var());
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

Literal* Renaming::normalize(Literal* l)
{
  CALL("Renaming::normalize(Literal*)");

  static Renaming n;
  n.reset();
  n.normalizeVariables(l);
  return n.apply(l);
}

Term* Renaming::normalize(Term* trm)
{
  CALL("Renaming::normalize(Term*)");

  static Renaming n;
  n.reset();
  n.normalizeVariables(trm);
  return n.apply(trm);
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
