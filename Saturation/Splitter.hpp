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

  int nameComponent(Clause* comp);
  BDDNode* getNameProp(int name);

  ClauseIterator handleNoSplit(Clause* cl);

  Clause* insertIntoIndex(Clause* cl, bool& newInserted, bool& modified);


  bool canSplitOut(Literal* lit);

  /** Names assigned to clauses stored in @b _variantIndex */
  DHMap<Clause*, int> _clauseNames;

  /**
   * Names for ground literals whose opposite counterparts haven't
   * been named yet
   *
   * See @b Splitter::nameComponent function.
   */
  DHMap<Literal*, int> _groundNames;

  /** Index containing names clauses. Name of a clause is stored in
   * @b _clauseNames */
  ClauseVariantIndex _variantIndex;
};

};

#endif /* __Splitter__ */
