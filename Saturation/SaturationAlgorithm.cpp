/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"
#include "../Shell/Statistics.hpp"

#include "SaturationAlgorithm.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;
using namespace Saturation;


SaturationAlgorithm::SaturationAlgorithm()
: _imgr(this), _passive(0), _generator(0), _fwSimplifier(0),
_bwSimplifier(0), _selector(0)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();
}

SaturationAlgorithm::~SaturationAlgorithm()
{
  delete _unprocessed;
  delete _active;
}

void SaturationAlgorithm::setLiteralSelector(LiteralSelector* selector)
{
  ASS(!_selector);
  _selector=selector;
}
void SaturationAlgorithm::setPassiveClauseContainer(PassiveClauseContainer* passiveContainer)
{
  ASS(!_passive);
  _passive=passiveContainer;
}
void SaturationAlgorithm::setGeneratingInferenceEngine(GeneratingInferenceEngine* generator)
{
  ASS(!_generator);
  _generator=generator;
  _generator->attach(this);
}
void SaturationAlgorithm::setForwardSimplificationEngine(ForwardSimplificationEngine* fwSimplifier)
{
  ASS(!_fwSimplifier);
  _fwSimplifier=fwSimplifier;
  _fwSimplifier->attach(this);
}
void SaturationAlgorithm::setBackwardSimplificationEngine(BackwardSimplificationEngine* bwSimplifier)
{
  ASS(!_bwSimplifier);
  _bwSimplifier=bwSimplifier;
  _bwSimplifier->attach(this);
}


ClauseContainer* DiscountSA::getSimplificationClauseContainer()
{ 
  return _active;
}

ClauseContainer* DiscountSA::getGenerationClauseContainer()
{
  return _active;
}


bool DiscountSA::processInactive(Clause* c)
{
  bool keep;
  ClauseIterator toAdd;
  _fwSimplifier->perform(c,keep,toAdd);
  _unprocessed->addClauses(toAdd);
  return keep;
}

void DiscountSA::activate(Clause* c)
{
  ClauseIterator toAdd;
  ClauseIterator toRemove;
  _bwSimplifier->perform(c,toRemove, toAdd);
  _active->removeClauses(toRemove);
  _unprocessed->addClauses(toAdd);
  
  _selector->select(c);
  
  toAdd=_generator->generateClauses(c);
  _unprocessed->addClauses(toAdd);
  
  _active->add(c);  
}

SaturationResult DiscountSA::saturate()
{
  CALL("DiscountSA::saturate");

  for (;;) {
    while (! _unprocessed->isEmpty()) {
      Clause* c = _unprocessed->pop();
      
      if (c->isEmpty()) {
    	return SaturationResult(Statistics::REFUTATION, c);
      }
      if(!processInactive(c)) {
	continue;
      }
      
      _passive->add(c);
    }
    
    if (env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
    if (_passive->isEmpty()) {
      return SaturationResult(Statistics::SATISFIABLE);
    }
    
    Clause* c = _passive->popSelected();
    if(!processInactive(c)) {
	continue;
    }
    activate(c);

    if (env.timeLimitReached()) {
      return SaturationResult(Statistics::TIME_LIMIT);
    }
  }
}
