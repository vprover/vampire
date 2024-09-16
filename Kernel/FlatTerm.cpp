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
  size_t size=sizeof(FlatTerm)+(num-1)*sizeof(TermList);

  return ALLOC_KNOWN(size,"FlatTerm");
}

/**
 * Destroy the FlatTerm object
 */
void FlatTerm::destroy()
{
  ASS_GE(_length,1);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size=sizeof(FlatTerm)+(_length-1)*sizeof(TermList);

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

FlatTerm::FlatTerm(size_t length)
: _length(length)
{
}

FlatTerm* FlatTerm::create(Term* t)
{
  size_t entries = t->weight();
  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    entries -= SortHelper::getEqualityArgumentSort(static_cast<Literal*>(t)).weight() - 1;
  }

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;
  res->_data[fti++] = TermList(t);

  SubtermIterator sti(t);
  while(sti.hasNext()) {
    res->_data[fti++] = sti.next();
  }
  ASS_EQ(fti, entries);

  return res;
}

FlatTerm* FlatTerm::create(TermList t)
{
  if(t.isTerm()) {
    ASS(!t.term()->isLiteral());
    return create(t.term());
  }
  ASS(t.isOrdinaryVar());


  FlatTerm* res=new(1) FlatTerm(1);
  res->_data[0] = t;

  return res;
}

FlatTerm* FlatTerm::create(TermStack ts)
{
  size_t entries=0;
  for (auto& tl : ts) {
    entries += tl.weight();
  }

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;

  for (auto& tl : ts) {
    res->_data[fti++] = tl;
    if (tl.isVar()) {
      continue;
    }
    ASS(!tl.term()->isLiteral());

    SubtermIterator sti(tl.term());
    while(sti.hasNext()) {
      res->_data[fti++] = sti.next();
    }
  }
  ASS_EQ(fti, entries);

  return res;
}

FlatTerm* FlatTerm::createUnexpanded(Term* t)
{
  size_t entries = t->weight();

  FlatTerm* res=new(entries) FlatTerm(entries);

  res->_data[0] = TermList(t);
  // NOTE: the first unexpanded argument is marked as empty
  if (t->arity()) {
    res->_data[1] = TermList::empty();
  }

  return res;
}

FlatTerm* FlatTerm::createUnexpanded(TermList t)
{
  if(t.isTerm()) {
    return createUnexpanded(t.term());
  }
  ASS(t.isOrdinaryVar());

  FlatTerm* res=new(1) FlatTerm(1);
  res->_data[0] = t;

  return res;
}

FlatTerm* FlatTerm::createUnexpanded(TermStack ts)
{
  size_t entries=0;
  for (auto& tl : ts) {
    entries += tl.weight();
  }

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;

  for (auto& tl : ts) {
    res->_data[fti]=tl;
    // NOTE: the first unexpanded argument is marked as empty
    if (tl.isTerm() && tl.term()->arity()) {
      res->_data[fti+1] = TermList::empty();
    }
    fti += tl.weight();
  }
  ASS_EQ(fti, entries);

  return res;
}

FlatTerm* FlatTerm::copy(const FlatTerm* ft)
{
  size_t entries=ft->_length;
  FlatTerm* res=new(entries) FlatTerm(entries);
  memcpy(res->_data, ft->_data, entries*sizeof(TermList));
  return res;
}

void FlatTerm::swapCommutativePredicateArguments()
{
  ASS(_data[0].isTerm() && _data[0].term()->isLiteral());
  ASS(static_cast<Literal*>(_data[0].term())->isEquality()); //as for now, the only commutative predicate is equality

  size_t firstStart = 1;
  size_t firstLen = _data[firstStart].weight();

  size_t secStart=firstStart+firstLen;
  size_t secLen = _data[secStart].weight();

  ASS_EQ(secStart+secLen,_length);

  static DArray<TermList> buf;
  if (firstLen > secLen) {
    buf.ensure(firstLen);
    memcpy(buf.array(), &_data[firstStart], firstLen*sizeof(TermList));
    memcpy(&_data[firstStart], &_data[secStart], secLen*sizeof(TermList));
    memcpy(&_data[firstStart+secLen], buf.array(), firstLen*sizeof(TermList));
  } else {
    buf.ensure(secLen);
    memcpy(buf.array(), &_data[secStart], secLen*sizeof(TermList));
    memcpy(&_data[firstStart+secLen], &_data[firstStart], firstLen*sizeof(TermList));
    memcpy(&_data[firstStart], buf.array(), secLen*sizeof(TermList));
  }
}

void FlatTerm::expand(size_t i)
{
  // NOTE: the first unexpanded argument is marked as empty
  if (i+1 >= _length || _data[i+1].isNonEmpty()) {
    return;
  }
  auto t = _data[i++].term();
  for (unsigned j = 0; j < t->arity(); j++) {
    TermList arg = *t->nthArgument(j);
    _data[i] = arg;
    if (arg.isTerm() && arg.term()->arity() && i+1 < _length) {
      _data[i+1] = TermList::empty();
    }
    i += _data[i].weight();
  }
}

};

