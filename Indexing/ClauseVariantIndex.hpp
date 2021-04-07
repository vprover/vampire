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
 * @file ClauseVariantIndex.hpp
 * Defines class ClauseVariantIndex.
 */


#ifndef __ClauseVariantIndex__
#define __ClauseVariantIndex__

#include "Forwards.hpp"

#include "Lib/Array.hpp"
#include "Lib/List.hpp"
#include "Lib/DHMap.hpp"

#include "Kernel/Term.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseVariantIndex
{
public:
  virtual ~ClauseVariantIndex() {};

  virtual void insert(Clause* cl) = 0;

  virtual ClauseIterator retrieveVariants(Literal* const * lits, unsigned length) = 0;
  ClauseIterator retrieveVariants(Clause* cl)
  {
    CALL("ClauseVariantIndex::retrieveVariants/1");

    // cout << "retrieveVariants for " <<  cl->toString() << endl;

    return retrieveVariants(cl->literals(), cl->length());
  }
protected:
  class ResultClauseToVariantClauseFn;
};


class SubstitutionTreeClauseVariantIndex : public ClauseVariantIndex
{
public:
  CLASS_NAME(SubstitutionTreeClauseVariantIndex);
  USE_ALLOCATOR(SubstitutionTreeClauseVariantIndex);

  SubstitutionTreeClauseVariantIndex() : _emptyClauses(0) {}
  virtual ~SubstitutionTreeClauseVariantIndex() override;

  virtual void insert(Clause* cl) override;

  ClauseIterator retrieveVariants(Literal* const * lits, unsigned length) override;

private:
  class SLQueryResultToClauseFn;

  Literal* getMainLiteral(Literal* const * lits, unsigned length);

  DHMap<Literal*, ClauseList*> _groundUnits;

  ZIArray<LiteralSubstitutionTree*> _strees;

  ClauseList* _emptyClauses;
};

class HashingClauseVariantIndex : public ClauseVariantIndex
{
public:
  CLASS_NAME(HashingClauseVariantIndex);
  USE_ALLOCATOR(HashingClauseVariantIndex);

  virtual ~HashingClauseVariantIndex() override;

  virtual void insert(Clause* cl) override;

  ClauseIterator retrieveVariants(Literal* const * lits, unsigned length) override;

private:
  struct VariableIgnoringComparator;

  typedef DHMap<unsigned, unsigned char> VarCounts; // overflows allowed

  unsigned termFunctorHash(Term* t, unsigned hash_begin) {
    unsigned func = t->functor();
    // cout << "will hash funtor " << func << endl;
    return Hash::hash((const unsigned char*)&func,sizeof(func),hash_begin);
  }

  unsigned computeHashAndCountVariables(unsigned var, VarCounts& varCnts, unsigned hash_begin) {
    const unsigned varHash = 1u;

    unsigned char* pcnt;
    if (varCnts.getValuePtr(var,pcnt)) {
      *pcnt = 1;
    } else {
      (*pcnt)++;
    }

    // cout << "will hash variable" << endl;

    return Hash::hash((const unsigned char*)&varHash,sizeof(varHash),hash_begin);
  }

  unsigned computeHashAndCountVariables(TermList* tl, VarCounts& varCnts, unsigned hash_begin);
  unsigned computeHashAndCountVariables(Literal* l, VarCounts& varCnts, unsigned hash_begin);

  unsigned computeHash(Literal* const * lits, unsigned length);

  DHMap<unsigned, ClauseList*> _entries;
};

};

#endif /* __ClauseVariantIndex__ */
