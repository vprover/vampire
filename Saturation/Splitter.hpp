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


  bool canSplitOut(Literal* lit);

  /** Names assigned to clauses stored in @b _variantIndex */
  DHMap<Clause*, int> _clauseNames;

  /** Names assigned to propositional predicates */
  DHMap<unsigned, int> _propPredNames;

  /** Clauses to be used as premises for replacing
   * positive predicate occurence by name */
  DHMap<unsigned, Clause*> _propPredPosNamePremises;

  /** Clauses to be used as premises for replacing
   * negative predicate occurence by name */
  DHMap<unsigned, Clause*> _propPredNegNamePremises;

  /** Index containing names clauses. Name of a clause is stored in
   * @b _clauseNames */
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __Splitter__ */
