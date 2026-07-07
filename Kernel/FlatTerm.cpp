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

#include "Lib/DArray.hpp"

#include "SortHelper.hpp"
#include "Term.hpp"

#include "FlatTerm.hpp"

namespace Kernel
{

using namespace Lib;

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

FlatTerm* FlatTerm::create(TermList t)
{
  size_t entries = t.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/true>(t.term());
  auto res = new FlatTerm(entries);

  size_t pos = 0;
  pushTerm</*mightBeLiteral=*/true>(res->_data->array(), pos, TermList(t));
  ASS_EQ(entries, pos);

  return res;
}

FlatTerm* FlatTerm::createEqReversed(Literal* lit)
{
  ASS(lit->isEquality());
  size_t entries = getEntryCount</*mightBeLiteral=*/true>(lit);
  auto res = new FlatTerm(entries);

  size_t pos = 0;
  pushTerm</*mightBeLiteral=*/true>(res->_data->array(), pos, TermList(lit));
  res->_data[0]._setTag(FUN);
  pos = FlatTerm::FUNCTION_ENTRY_COUNT;

  // If literal is equality, we add a type argument to properly match with
  // two variable equalities. This has to be done also in the code tree.
  pushTerm</*mightBeLiteral=*/false>(res->_data->array(), pos, SortHelper::getEqualityArgumentSort(lit));
  pushTerm</*mightBeLiteral=*/false>(res->_data->array(), pos, lit->termArg(1));
  pushTerm</*mightBeLiteral=*/false>(res->_data->array(), pos, lit->termArg(0));

  return res;
}

FlatTerm* FlatTerm::create(TermStack ts)
{
  size_t entries=0;
  for (auto& tl : ts) {
    entries += tl.isVar() ? 1 : getEntryCount</*mightBeLiteral=*/true>(tl.term());
  }

  auto res = new FlatTerm(entries);
  size_t fti=0;

  for (auto& tl : ts) {
    pushTerm</*mightBeLiteral=*/true>(res->_data->array(), fti, tl);
  }
  ASS_EQ(fti, entries);

  return res;
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
