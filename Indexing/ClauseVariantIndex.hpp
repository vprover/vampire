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

  ClauseIterator retrieveVariants(Literal* const * lits, unsigned length);

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

  ClauseIterator retrieveVariants(Literal* const * lits, unsigned length);

private:
  typedef DHMap<unsigned, unsigned> VarCounts;

  unsigned computeHash(Literal* l, VarCounts& varCnts);

  unsigned computeHash(Literal* const * lits, unsigned length);

  DHMap<unsigned, ClauseList*> _entries;
};

};

#endif /* __ClauseVariantIndex__ */
