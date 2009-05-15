/**
 * @file ClauseVariantIndex.hpp
 * Defines class ClauseVariantIndex.
 */


#ifndef __ClauseVariantIndex__
#define __ClauseVariantIndex__

#include "../Forwards.hpp"

#include "../Lib/Array.hpp"
#include "../Lib/List.hpp"

namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseVariantIndex
{
public:
  ClauseVariantIndex() : _emptyClauses(0) {}
  ~ClauseVariantIndex();

  void insert(Clause* cl);

  ClauseIterator retrieveVariants(Literal** lits, unsigned length);

private:
  Literal* getMainLiteral(Literal** lits, unsigned length);
  class SLResultToVariantClauseFn;

  ZIArray<LiteralSubstitutionTree*> _strees;

  ClauseList* _emptyClauses;
};

};

#endif /* __ClauseVariantIndex__ */
