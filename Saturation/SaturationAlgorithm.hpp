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
#include "../Inferences/InferenceEngine.hpp"

#include "Limits.hpp"
#include "SaturationResult.hpp"

#ifdef VDEBUG
#include<iostream>
#include "../Test/Output.hpp"
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
  SaturationAlgorithm(PassiveClauseContainer* passiveContainer, LiteralSelector* selector);
  virtual ~SaturationAlgorithm();
  
  void setGeneratingInferenceEngine(GeneratingInferenceEngine* generator);
  void setForwardSimplificationEngine(ForwardSimplificationEngine* fwSimplifier);
  void setBackwardSimplificationEngine(BackwardSimplificationEngine* bwSimplifier);
  
  PlainEvent safePointEvent;
  
  virtual SaturationResult saturate() = 0;

  void addClauses(ClauseIterator cit)
  { _unprocessed->addClauses(cit); }
  
  virtual ClauseContainer* getSimplificationClauseContainer() = 0;
  virtual ClauseContainer* getGenerationClauseContainer() = 0;
  
  Limits* getLimits() { return &_limits; }
  IndexManager* getIndexManager() { return &_imgr; }
  
#ifdef VDEBUG
  void enableContainerPrintouts()
  {
    _active->addedEvent.subscribe(this,&SaturationAlgorithm::onActiveAdded);
    _passive->addedEvent.subscribe(this,&SaturationAlgorithm::onPassiveAdded);
    _passive->removedEvent.subscribe(this,&SaturationAlgorithm::onPassiveRemoved);
    _unprocessed->addedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedAdded);
    _unprocessed->removedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedRemoved);
  }
  void onActiveAdded(Clause* c)
  {
    cout<<"Active added: "<<Test::Output::toString(c)<<endl;
  }
  void onPassiveAdded(Clause* c)
  {
    cout<<"Passive added: "<<Test::Output::toString(c)<<endl;
  }
  void onPassiveRemoved(Clause* c)
  {
    cout<<"Passive removed: "<<Test::Output::toString(c)<<endl;
  }
  void onUnprocessedAdded(Clause* c)
  {
    cout<<"Unprocessed added: "<<Test::Output::toString(c)<<endl;
  }
  void onUnprocessedRemoved(Clause* c)
  {
    cout<<"Unprocessed removed: "<<Test::Output::toString(c)<<endl;
  }
#endif
  
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
  DiscountSA(PassiveClauseContainer* passiveContainer, LiteralSelector* selector)
    : SaturationAlgorithm(passiveContainer,selector) {}
  SaturationResult saturate();
  
  ClauseContainer* getSimplificationClauseContainer();
  ClauseContainer* getGenerationClauseContainer();
  
protected:
  bool processInactive(Clause* c);
  void activate(Clause* c);
};

  
};

#endif /*__SaturationAlgorithm__*/
