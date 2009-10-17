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
  ClauseIterator doSplitting(Clause* cl);
private:
  Clause* getComponent(Clause* cl, Literal** lits, unsigned compLen, int& name, bool& newComponent);

  ClauseIterator handleNoSplit(Clause* cl);

  Clause* insertIntoIndex(Clause* cl, bool& newInserted, bool& modified);


  bool canSplitOut(Literal* lit);
  bool isBipolar(Literal* lit);

  /** Names assigned to clauses stored in @b _variantIndex */
  DHMap<Clause*, int> _clauseNames;

  /** Literals with assigned names such that positive and negative
   * ones share the same name */
  DHMap<Literal*, int> _bipolarNames;

  /** Premises for naming literals with bipolar names */
  DHMap<Literal*, Clause*> _bipolarPremises;

  /** Index containing names clauses. Name of a clause is stored in
   * @b _clauseNames */
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __Splitter__ */
