/**
 * @file Splitter.hpp
 * Defines class Splitter.
 */


#ifndef __Splitter__
#define __Splitter__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "../Indexing/ClauseVariantIndex.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class Splitter
{
public:
  void doSplitting(Clause* cl, ClauseIterator& newComponents, ClauseIterator& modifiedComponents);
private:
  void getPropPredName(Literal* lit, int& name, Clause*& premise, bool& newPremise);

  void handleNoSplit(Clause* cl, ClauseIterator& newComponents,
		ClauseIterator& modifiedComponents);

  Clause* insertIntoIndex(Clause* cl, bool& newInserted, bool& modified);

  DHMap<Clause*, int, PtrIdentityHash> _clauseNames;
  DHMap<unsigned, int, IdentityHash> _propPredNames;

  /** Clauses to be used as premises for replacing
   * positive predicate occurence by name */
  DHMap<unsigned, Clause*, IdentityHash> _propPredPosNamePremises;

  /** Clauses to be used as premises for replacing
   * negative predicate occurence by name */
  DHMap<unsigned, Clause*, IdentityHash> _propPredNegNamePremises;
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __Splitter__ */
