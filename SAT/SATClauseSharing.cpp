
/*
 * File SATClauseSharing.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file SATClauseSharing.cpp
 * Implements class SATClauseSharing.
 */

#include "Lib/Hash.hpp"

#include "SATClauseSharing.hpp"

namespace SAT
{

SATClause* SATClauseSharing::insert(SATClause* c)
{
  SATClause* res=_storage.insert(c);
  if(res!=c) {
    c->destroy();
  }
  return res;
}

void SATClauseSharing::wipe()
{
  ClauseSet::Iterator it(_storage);
  while(it.hasNext()) {
    SATClause* cl=it.next();
    if(!cl->kept()) {
      cl->destroy();
    }
  }
  _storage.~ClauseSet();
  ::new(&_storage) ClauseSet();
}


SATClauseSharing* SATClauseSharing::getInstance()
{
  static SATClauseSharing* inst=0;
  if(!inst) {
    inst=new SATClauseSharing();
  }
  return inst;
}


unsigned SATClauseSharing::Hasher::hash(SATClause* c)
{
  return Hash::hash(reinterpret_cast<const unsigned char*>(c->literals()),
	  c->length()*sizeof(SATLiteral));
}

bool SATClauseSharing::Hasher::equals(SATClause* c1, SATClause* c2)
{
  if(c1->length()!=c2->length()) {
    return false;
  }
  for(int i=c1->length();i>=0;i--) {
    if((*c1)[i]!=(*c2)[i]) {
      return false;
    }
  }
  return true;
}


}
