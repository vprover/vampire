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
  RSTAT_CTR_INC("rename");
  Applicator a(this);
  return SubstHelper::apply(lit, a);
}

Term* Renaming::apply(Term* trm)
{
  CALL("Renaming::apply(Term*...)");
  Applicator a(this);
  return SubstHelper::apply(trm, a);
}

TermList Renaming::apply(TermList trm)
{
  CALL("Renaming::apply(TermList...)");
  Applicator a(this);
  return SubstHelper::apply(trm, a);
}

bool Renaming::identity() const
{
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    if(from!=to) {
      return false;
    }
  }
  return true;
}

/**
 * Make the renaming normalize variables of term or literal @c t
 */
void Renaming::normalizeVariables(const Term* t)
{
  VariableIterator vit(t);
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
}

Literal* Renaming::normalize(Literal* l)
{
  CALL("Renaming::normalize(Literal*)");

  Renaming n;
  n.normalizeVariables(l);
  return n.apply(l);
}

Term* Renaming::normalize(Term* l)
{
  CALL("Renaming::normalize(Term*)");

  Renaming n;
  n.normalizeVariables(l);
  return n.apply(l);
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

std::string Renaming::toString() const
{
  std::string res;
  VariableMap::Iterator mit(_data);
  while(mit.hasNext()) {
    unsigned from, to;
    mit.next(from, to);
    res+=Int::toString(from)+" -> "+Int::toString(to)+"\n";
  }
  return res;
}

#endif

}
