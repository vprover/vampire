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
 * @file FlatTerm.cpp

 * Implements class FlatTerm.
 */

#include <cstring>

#include "Lib/Allocator.hpp"
#include "Lib/DArray.hpp"

#include "Term.hpp"
#include "TermIterators.hpp"

#include "FlatTerm.hpp"

namespace Kernel
{

using namespace Lib;

/**
 * Allocate a FlatTerm object having @b num entries.
 */
void* FlatTerm::operator new(size_t sz,unsigned num)
{
  ASS_GE(num,1);
  ASS_EQ(sz, sizeof(FlatTerm));

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(num-1)*sizeof(Entry);

  return ALLOC_KNOWN(size,"FlatTerm");
}

/**
 * Destroy the FlatTerm object
 */
void FlatTerm::destroy()
{
  ASS_GE(_length,1);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(_length-1)*sizeof(Entry);

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

FlatTerm::FlatTerm(size_t length)
: _length(length)
{
}

size_t FlatTerm::getEntryCount(Term* t)
{
  //FUNCTION_ENTRY_COUNT entries per function and one per variable
  return t->weight()*FUNCTION_ENTRY_COUNT-(FUNCTION_ENTRY_COUNT-1)*t->numVarOccs();
}

FlatTerm* FlatTerm::create(Term* t)
{
  size_t entries=getEntryCount(t);

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;
  res->_data[fti++]=Entry(FUN,
      t->isLiteral() ? static_cast<Literal*>(t)->header() : t->functor());
  res->_data[fti++]=Entry(t);
  res->_data[fti++]=Entry(FUN_RIGHT_OFS, getEntryCount(t));

  SubtermIterator sti(t);
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
  if(t.isTerm()) {
    return create(t.term());
  }
  ASS(t.isOrdinaryVar());


  FlatTerm* res=new(1) FlatTerm(1);
  res->_data[0]=Entry(VAR, t.var());

  return res;
}

FlatTerm* FlatTerm::createUnexpanded(Term* t)
{
  size_t entries=getEntryCount(t);

  FlatTerm* res=new(entries) FlatTerm(entries);

  res->_data[0]=Entry(FUN_UNEXPANDED,
      t->isLiteral() ? static_cast<Literal*>(t)->header() : t->functor());
  res->_data[1]=Entry(t);
  res->_data[2]=Entry(FUN_RIGHT_OFS, entries);

  return res;
}

FlatTerm* FlatTerm::createUnexpanded(TermList t)
{
  if(t.isTerm()) {
    return createUnexpanded(t.term());
  }
  ASS(t.isOrdinaryVar());

  FlatTerm* res=new(1) FlatTerm(1);
  res->_data[0]=Entry(VAR, t.var());

  return res;
}

FlatTerm* FlatTerm::copy(const FlatTerm* ft)
{
  size_t entries=ft->_length;
  FlatTerm* res=new(entries) FlatTerm(entries);
  memcpy(res->_data, ft->_data, entries*sizeof(Entry));
  return res;
}

void FlatTerm::swapCommutativePredicateArguments()
{
  ASS_EQ((*this)[0]._tag(), FUN);
  ASS_EQ((*this)[0]._number()|1, 1); //as for now, the only commutative predicate is equality

  size_t firstStart=3;
  size_t firstLen;
  if((*this)[firstStart]._tag()==FUN) {
    ASS_EQ((*this)[firstStart+2]._tag(), FUN_RIGHT_OFS);
    firstLen=(*this)[firstStart+2]._number();
  }
  else {
    ASS_EQ((*this)[firstStart]._tag(), VAR);
    firstLen=1;
  }

  size_t secStart=firstStart+firstLen;
  size_t secLen;

  if((*this)[secStart]._tag()==FUN) {
    ASS_EQ((*this)[secStart+2]._tag(), FUN_RIGHT_OFS);
    secLen=(*this)[secStart+2]._number();
  }
  else {
    ASS_EQ((*this)[secStart]._tag(), VAR);
    secLen=1;
  }
  ASS_EQ(secStart+secLen,_length);

  static DArray<Entry> buf;
  if(firstLen>secLen) {
    buf.ensure(firstLen);
    memcpy(buf.array(), &_data[firstStart], firstLen*sizeof(Entry));
    memcpy(&_data[firstStart], &_data[secStart], secLen*sizeof(Entry));
    memcpy(&_data[firstStart+secLen], buf.array(), firstLen*sizeof(Entry));
  }
  else {
    buf.ensure(secLen);
    memcpy(buf.array(), &_data[secStart], secLen*sizeof(Entry));
    memcpy(&_data[firstStart+secLen], &_data[firstStart], firstLen*sizeof(Entry));
    memcpy(&_data[firstStart], buf.array(), secLen*sizeof(Entry));
  }
}

void FlatTerm::Entry::expand()
{
  if (_tag()==FUN) {
    return;
  }
  ASS(_tag()==FUN_UNEXPANDED);
  ASS(this[1]._tag()==FUN_TERM_PTR);
  ASS(this[2]._tag()==FUN_RIGHT_OFS);
  Term* t = this[1]._term();
  size_t p = FlatTerm::FUNCTION_ENTRY_COUNT;
  for (unsigned i = 0; i < t->arity(); i++) {
    auto arg = t->nthArgument(i);
    if (arg->isVar()) {
      ASS(arg->isOrdinaryVar());
      this[p++] = Entry(VAR, arg->var());
    }
    else {
      ASS(arg->isTerm());
      this[p] = Entry(FUN_UNEXPANDED, arg->term()->functor());
      this[p+1] = Entry(arg->term());
      this[p+2] = Entry(FUN_RIGHT_OFS, getEntryCount(arg->term()));
      p += this[p+2]._number();
    }
  }
  ASS_EQ(p,this[2]._number());
  _setTag(FUN);
}

};

