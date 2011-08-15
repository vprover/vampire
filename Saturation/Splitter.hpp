/**
 * @file Splitter.hpp
 * Defines class Splitter.
 */


#ifndef __Splitter__
#define __Splitter__

#include "Forwards.hpp"

namespace Saturation {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Shell;

class Splitter
{
public:
  virtual ~Splitter() {}

  virtual void init(SaturationAlgorithm* sa);

  virtual bool doSplitting(Clause* cl) = 0;

  /**
   * Return true if the splitter handles the empty clause and
   * it should not be further processed
   */
  virtual bool handleEmptyClause(Clause* cl) { return false; }

  virtual void onClauseReduction(Clause* cl, Clause* premise, Clause* replacement=0);
  virtual void onClauseReduction(Clause* cl, ClauseIterator premises, Clause* replacement=0) {}
  virtual void onNewClause(Clause* cl) {}
  virtual void onAllProcessed() {}

  const Options& getOptions() const;
protected:

  bool splitPositive();

  virtual bool splittingAllowed(Clause* cl);

  bool isAnswerLiteral(Literal* lit);

  SaturationAlgorithm* _sa;
  AnswerLiteralManager* _ansLitMgr;
};

};

#endif /* __Splitter__ */
