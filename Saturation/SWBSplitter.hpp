/**
 * @file SWBSplitter.hpp
 * Defines class SWBSplitter.
 */

#ifndef __SWBSplitter__
#define __SWBSplitter__

#include <utility>

#include "../Forwards.hpp"

#include "Splitter.hpp"

#define REPORT_SPLITS 0

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

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

  virtual void buildAndInsertComponents(Clause* cl, CompRec* comps, unsigned compCnt, bool firstIsMaster) = 0;

  virtual bool handleNoSplit(Clause* cl) = 0;

  bool canSplitOut(Literal* lit);
  virtual bool canStandAlone(Literal* lit);
  virtual bool standAloneObligations();
};

}

#endif // __SWBSplitter__
