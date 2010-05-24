/**
 * @file SWBSplitter.hpp
 * Defines class SWBSplitter.
 */

#ifndef __SWBSplitter__
#define __SWBSplitter__

#include <utility>

#include "Forwards.hpp"

#include "Splitter.hpp"

#define REPORT_SPLITS 0

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

/**
 * Descendant objects of the @b SWBSplitter class perform the
 * splitting without backtracking
 *
 * If BDDs are used for propositional predicates, the
 * @b SWBSplitterWithBDDs object should be used, otherwise
 * it should be @b SWBSplitterWithoutBDDs.
 */
class SWBSplitter : public Splitter
{
public:
  bool doSplitting(Clause* cl);
protected:
  struct CompRec
  {
    CompRec() {}
    CompRec(Literal** lits, unsigned len) : lits(lits), len(len) {}
    Literal** lits;
    unsigned len;
  };

  /**
   * Build clauses based on the component info in @b comps
   * and put them into the saturation algorithm
   *
   * If @b firstIsMaster is true, the record @b comps[0]
   * has to be used for the master component.
   */
  virtual void buildAndInsertComponents(Clause* cl, CompRec* comps,
      unsigned compCnt, bool firstIsMaster) = 0;

  /**
   * Perform necessary actions on a clause that is not being split
   *
   * When true is returned, the clause @b cl should not be kept in the
   * run of the saturation algorithm.
   */
  virtual bool handleNoSplit(Clause* cl) { return false; }

  bool canSplitOut(Literal* lit);
  virtual bool canStandAlone(Literal* lit);
  virtual bool standAloneObligations();
};

}

#endif // __SWBSplitter__
