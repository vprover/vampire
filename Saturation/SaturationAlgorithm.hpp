/**
 * @file SaturationAlgorithm.hpp
 * Defines class SaturationAlgorithm
 *
 */

#ifndef __SaturationAlgorithm__
#define __SaturationAlgorithm__

#include "../Forwards.hpp"

#include "../Kernel/Clause.hpp"
#include "../Lib/Event.hpp"
#include "../Indexing/IndexManager.hpp"
#include "../Inferences/InferenceEngine.hpp"

#include "Limits.hpp"
#include "SaturationResult.hpp"

#if VDEBUG
#include<iostream>
#endif

namespace Saturation
{

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Inferences;

class SaturationAlgorithm
{
public:
  SaturationAlgorithm(PassiveClauseContainerSP passiveContainer, LiteralSelectorSP selector);
  virtual ~SaturationAlgorithm();

  void setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator);
  void setForwardSimplificationEngine(ForwardSimplificationEngineSP fwSimplifier);
  void setBackwardSimplificationEngine(BackwardSimplificationEngineSP bwSimplifier);

  virtual SaturationResult saturate() = 0;

  void addClauses(ClauseIterator cit)
  { _unprocessed->addClauses(cit); }

  virtual ClauseContainer* getSimplificationClauseContainer() = 0;
  virtual ClauseContainer* getGenerationClauseContainer() = 0;

  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return &_imgr; }

  static SaturationAlgorithmSP createFromOptions();

private:
  Limits _limits;
  IndexManager _imgr;
protected:
  UnprocessedClauseContainer* _unprocessed;
  PassiveClauseContainerSP _passive;
  ActiveClauseContainer* _active;

  GeneratingInferenceEngineSP _generator;
  ForwardSimplificationEngineSP _fwSimplifier;
  BackwardSimplificationEngineSP _bwSimplifier;

  LiteralSelectorSP _selector;
};


};

#endif /*__SaturationAlgorithm__*/
