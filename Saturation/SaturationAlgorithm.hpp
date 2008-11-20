/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Inference/InferenceEngine.hpp"

#include "Limits.hpp"
#include "ClauseContainer.hpp"
#include "SaturationResult.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inference;

class SaturationAlgorithm
{
public:
  SaturationAlgorithm(PassiveClauseContainer* passiveContainer,
	  GeneratingInferenceEngine* generator, ForwardSimplificationEngine* fwSimplifier,
	  BackwardSimplificationEngine* bwSimplifier, LiteralSelector* selector);
  virtual ~SaturationAlgorithm();
  
  PlainEvent safePointEvent;
  
  virtual SaturationResult saturate() = 0;

  void addClauses(ClauseIterator cit)
  { _unprocessed->addClauses(cit); }
  
  virtual ClauseContainer* getSimplificationClauseContainer() = 0;
  virtual ClauseContainer* getGenerationClauseContainer() = 0;
  
  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return &_imgr; }
  
private:
  Limits _limits;
  IndexManager _imgr;
protected:  
  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainer* _passive;
  ActiveClauseContainer* _active;
  
  GeneratingInferenceEngine* _generator;
  ForwardSimplificationEngine* _fwSimplifier;
  BackwardSimplificationEngine* _bwSimplifier;

  LiteralSelector* _selector;
};


class DiscountSA
: public SaturationAlgorithm
{
public:
  SaturationResult saturate();
protected:
  bool processInactive(Clause* c);
  void activate(Clause* c);
};

  
};

#endif /*__SaturationAlgorithm__*/
