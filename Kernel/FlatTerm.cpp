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

#include "SortHelper.hpp"
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
  ASS_GE(num,0);
  ASS_EQ(sz, sizeof(FlatTerm));

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size = sizeof(FlatTerm);
  if (num > 0) {
    size += (num-1)*sizeof(Entry);
  }

  return ALLOC_KNOWN(size,"FlatTerm");
}

/**
 * Destroy the FlatTerm object
 */
void FlatTerm::destroy()
{
  ASS_GE(_length,0);

  //one entry is already accounted for in the size of the FlatTerm object
  size_t size = sizeof(FlatTerm);
  if (_length > 0) {
    size += (_length-1)*sizeof(Entry);
  }

  DEALLOC_KNOWN(this, size,"FlatTerm");
}

template<bool mightBeLiteral>
size_t FlatTerm::getEntryCount(Term* t)
{
  if constexpr (mightBeLiteral) {
    //FUNCTION_ENTRY_COUNT entries per function and one per variable
    if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
      // we add the type to the flat term for equalities as an extra,
      // which requires some additional calculation
      auto sort = SortHelper::getEqualityArgumentSort(static_cast<Literal*>(t));
      unsigned numVarOccs = t->numVarOccs();
      if (!t->isTwoVarEquality()) {
        // in case of non-two-var equalities, the variables in
        // the type are not counted by Term::numVarOccs
        numVarOccs += sort.isVar() ? 1 : sort.term()->numVarOccs();
      }
      // the weight is corrected to be conservative in the
      // monomorphic case, we uncorrect it by adding 1
      return (t->weight()+1)*FUNCTION_ENTRY_COUNT-(FUNCTION_ENTRY_COUNT-1)*numVarOccs;
    }
  } else {
    ASS(!t->isLiteral());
  }
  return t->weight()*FUNCTION_ENTRY_COUNT-(FUNCTION_ENTRY_COUNT-1)*t->numVarOccs();
}

FlatTerm* FlatTerm::createUnexpanded(TermList t)
{
  size_t entries = t.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/true>(t.term());
  auto res = new(entries) FlatTerm(entries);

  size_t pos = 0;
  pushTerm</*mightBeLiteral=*/true>(res->_data, pos, TermList(t));
  ASS_EQ(entries, pos);

  return res;
}

FlatTerm* FlatTerm::createUnexpanded(TermStack ts)
{
  size_t entries=0;
  for (auto& tl : ts) {
    entries += tl.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/true>(tl.term());
  }

  FlatTerm* res=new(entries) FlatTerm(entries);
  size_t fti=0;

  for (auto& tl : ts) {
    pushTerm</*mightBeLiteral=*/true>(res->_data, fti, tl);
  }
  ASS_EQ(fti, entries);

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
  // expand the top-level to get rid of unknown arguments
  (*this)[0].expand();

  ASS_EQ((*this)[0]._tag(), FUN);
  ASS_EQ((*this)[0]._number()|1, 1); //as for now, the only commutative predicate is equality

  ASS((*this)[1]._term()->isLiteral());
  auto lit = static_cast<Literal*>((*this)[1]._term());
  ASS(lit->isEquality());

  auto getLen = [this](size_t start) -> unsigned {
    if ((*this)[start]._tag() == FUN || (*this)[start]._tag() == FUN_UNEXPANDED) {
      ASS_EQ((*this)[start+2]._tag(), FUN_RIGHT_OFS);
      return (*this)[start+2]._number();
    }
    ASS_EQ((*this)[start]._tag(), VAR);
    return 1;
  };

  size_t firstStart = 3;
  auto sort = SortHelper::getEqualityArgumentSort(lit);
  firstStart += sort.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/false>(sort.term());

  size_t firstLen = getLen(firstStart);

  size_t secStart = firstStart+firstLen;
  size_t secLen = getLen(secStart);

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
  ASS_EQ(_tag(), FUN_UNEXPANDED);
  ASS_EQ(this[1]._tag(), FUN_TERM_PTR);
  ASS_EQ(this[2]._tag(), FUN_RIGHT_OFS);
  Term* t = this[1]._term();
  size_t pos = FlatTerm::FUNCTION_ENTRY_COUNT;

  // If literal is equality, we add a type argument
  // to properly match with two variable equalities.
  // This has to be done also in the code tree.
  if (t->isLiteral() && static_cast<Literal*>(t)->isEquality()) {
    pushTerm</*mightBeLiteral=*/false>(this, pos, SortHelper::getEqualityArgumentSort(static_cast<Literal*>(t)));
  }

  for (unsigned i = 0; i < t->arity(); i++) {
    pushTerm</*mightBeLiteral=*/false>(this, pos, *t->nthArgument(i));
  }
  ASS_EQ(pos,this[2]._number());
  _setTag(FUN);
}

};
