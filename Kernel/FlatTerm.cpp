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
  ASS_GE(num,1);
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
  ASS_GE(_length,1);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(_length-1)*sizeof(FlatTerm::Entry);

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

FlatTerm::FlatTerm(size_t length)
: _length(length)
{
  CALL("FlatTerm::FlatTerm");
}

size_t FlatTerm::getEntryCount(Term* t)
{
  //functionEntryCount entries per function and one per variable
  return t->weight()*functionEntryCount-(functionEntryCount-1)*t->vars();
}

FlatTerm* FlatTerm::create(Term* t)
{
  CALL("FlatTerm::create(Term)");

  size_t entries=getEntryCount(t);

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;
  res->_data[fti++]=Entry(FUN,
      t->isLiteral() ? static_cast<Literal*>(t)->header() : t->functor());
  res->_data[fti++]=Entry(t);
  res->_data[fti++]=Entry(FUN_RIGHT_OFS, getEntryCount(t));

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
      res->_data[fti++]=Entry(FUN_RIGHT_OFS, getEntryCount(s.term()));
    }
  }
  ASS_EQ(fti, entries);

  return res;
}

FlatTerm* FlatTerm::create(TermList t)
{
  CALL("FlatTerm::create(TermList)");

  if(t.isTerm()) {
    return create(t.term());
  }
  ASS(t.isOrdinaryVar());


  FlatTerm* res=new(1) FlatTerm(1);
  res->_data[0]=Entry(VAR, t.var());

  return res;
}


};

