/**
 * @file FlatTerm.cpp

 * Implements class FlatTerm.
 */



#include "../Lib/Allocator.hpp"

#include "Term.hpp"

#include "FlatTerm.hpp"

namespace Kernel
{

using namespace Lib;

/**
 * Allocate a FlatTerm object having @b num entries.
 */
void* FlatTerm::operator new(size_t sz,unsigned num)
{
  CALL("FlatTerm::operator new");
  ASS_G(num,1);
  ASS_EQ(sz, sizeof(FlatTerm));

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(num-1)*sizeof(FlatTerm::Entry);

  return ALLOC_KNOWN(size,"FlatTerm");
}

/**
 * Destroy the FlatTerm object
 */
void FlatTerm::destroy()
{
  CALL("FlatTerm::destroy");
  ASS_G(_length,1);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(_length-1)*sizeof(FlatTerm::Entry);

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

FlatTerm::FlatTerm(size_t length)
: _length(length)
{
  CALL("FlatTerm::FlatTerm");
}

FlatTerm* FlatTerm::create(Term* t)
{
  CALL("FlatTerm::create");

  //one for start, one for end, two per function and one per variable
  size_t entries=2+t->weight()*2-t->vars();

  FlatTerm* res=new(entries) FlatTerm(entries);
  res->_literal=t->isLiteral();
  size_t fti=0;
  res->_data[fti++]._info.tag=EDGE;
  res->_data[fti++]=Entry(FUN,
      res->_literal ? static_cast<Literal*>(t)->header() : t->functor());
  res->_data[fti++]=Entry(t);

  Term::SubtermIterator sti(t);
  while(sti.hasNext()) {
    ASS_L(fti, entries);
    TermList s=sti.next();
    if(s.isVar()) {
      ASS(s.isOrdinaryVar());
      res->_data[fti++]=Entry(VAR, s.var());
    }
    else {
      ASS(s.isTerm());
      res->_data[fti++]=Entry(FUN, s.term()->functor());
      res->_data[fti++]=Entry(s.term());
    }
  }
  res->_data[fti]._info.tag=EDGE;
  ASS_EQ(fti+1, entries);

  return res;
}


};

