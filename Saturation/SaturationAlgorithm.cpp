/**
 * @file SaturationAlgorithm.cpp
 * Implementing SaturationAlgorithm class.
 */

#include "../Lib/Environment.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Kernel/Clause.hpp"
#include "../Kernel/LiteralSelector.hpp"

#include "SaturationAlgorithm.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Saturation;


SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainer* passive,
	GeneratingInferenceEngine* generator, ForwardSimplificationEngine* fwSimplifier,
	BackwardSimplificationEngine* bwSimplifier, LiteralSelector* selector)
: _imgr(this), _passive(passive), _generator(generator), _fwSimplifier(fwSimplifier),
_bwSimplifier(bwSimplifier), _selector(selector)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();
  
  _generator->attach(this);
  _fwSimplifier->attach(this);
  _bwSimplifier->attach(this);
}


SaturationAlgorithm::~SaturationAlgorithm()
{
  delete _unprocessed;
  delete _passive;
  delete _active;
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
    	return SaturationResult(SaturationResult::REFUTATION, c);
      }
      if(!processInactive(c)) {
	continue;
      }
      
      _passive->add(c);
    }
    
    if (env.timeLimitReached()) {
      return SaturationResult(SaturationResult::TIME_LIMIT);
    }
    if (_passive->isEmpty()) {
      return SaturationResult(SaturationResult::SATISFIABLE);
    }
    
    Clause* c = _passive->popSelected();
    if(!processInactive(c)) {
	continue;
    }
    activate(c);

    if (env.timeLimitReached()) {
      return SaturationResult(SaturationResult::TIME_LIMIT);
    }
  }
}
