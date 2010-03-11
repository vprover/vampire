/**
 * @file SWBSplitterWithoutBDDs.hpp
 * Defines class SWBSplitterWithoutBDDs.
 */


#ifndef __SWBSplitterWithoutBDDs__
#define __SWBSplitterWithoutBDDs__

#include "../Forwards.hpp"

#include "../Lib/DHMap.hpp"

#include "SWBSplitter.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class SWBSplitterWithoutBDDs : public SWBSplitter
{
protected:
  void buildAndInsertComponents(Clause* cl, CompRec* comps, unsigned compCnt, bool firstIsMaster);

  bool handleNoSplit(Clause* cl);

  //overrides SWBSplitter::canStandAlone
  bool canStandAlone(Literal* lit);
  //overrides SWBSplitter::standAloneObligations
  bool standAloneObligations();

private:

  struct CompNameRec
  {
    CompNameRec() : name(0), namingClause(0) {}
    CompNameRec(int name, Clause* namingClause) : name(name), namingClause(namingClause) {}
    bool isEmpty() { return name==0; }

    int name;
    Clause* namingClause;
  };

  CompNameRec getNamedComponent(Clause* cl, CompRec cr);
  CompNameRec createNamedComponent(Clause* cl, CompRec cr, int knownName=0);

  Literal* getNameLiteral(int name, bool forMaster);
  int getNewName();

  int nameComponent(Clause* comp);
  BDDNode* getNameProp(int name);

  /** Names assigned to clauses stored in @b _variantIndex */
  DHMap<Clause*, int> _clauseNames;

  /**
   * Names for ground literals
   */
  DHMap<Literal*, CompNameRec> _groundNames;
};

};

#endif /* __SWBSplitterWithoutBDDs__ */
