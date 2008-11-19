/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "../Lib/Forwards.hpp"
#include "../Kernel/Forwards.hpp"

#include "../Lib/Event.hpp"
#include "../Indexing/IndexManager.hpp"

#include "Limits.hpp"
#include "ClauseContainer.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;

class SaturationAlgorithm
{
public:
  SaturationAlgorithm(PassiveClauseContainer* passiveContainer);
  virtual ~SaturationAlgorithm();
  
  PlainEvent safePointEvent;
  
  virtual void saturate() = 0;

  void addClauses(ClauseIterator cit)
  { _unprocessed->addClauses(cit); }
  
  virtual ClauseContainer* getSimplificationClauseContainer() = 0;
  virtual ClauseContainer* getGenerationClauseContainer() = 0;
  
  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return &_imgr; }
  
private:
  Limits _limits;
  IndexManager _imgr;
  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainer* _passive;
  ActiveClauseContainer* _active;
};
  
};

#endif /*__SaturationAlgorithm__*/
