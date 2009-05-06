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


SaturationAlgorithm::SaturationAlgorithm(PassiveClauseContainerSP passiveContainer,
	LiteralSelectorSP selector)
: _imgr(this), _passive(passiveContainer), _bwSimplifiers(0), _selector(selector)
{
  _unprocessed=new UnprocessedClauseContainer();
  _active=new ActiveClauseContainer();

  _active->attach(this);
  _passive->attach(this);

#if VDEBUG
//  _active->addedEvent.subscribe(this,&SaturationAlgorithm::onActiveAdded);
//  _passive->addedEvent.subscribe(this,&SaturationAlgorithm::onPassiveAdded);
//  _passive->removedEvent.subscribe(this,&SaturationAlgorithm::onPassiveRemoved);
//  _unprocessed->addedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedAdded);
//  _unprocessed->removedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedRemoved);
//  _unprocessed->selectedEvent.subscribe(this,&SaturationAlgorithm::onUnprocessedSelected);
#endif

}

SaturationAlgorithm::~SaturationAlgorithm()
{
  env.statistics->finalActiveClauses=_active->size();
  env.statistics->finalPassiveClauses=_passive->size();

  _active->detach();
  _passive->detach();

  if(_generator) {
    _generator->detach();
  }
  if(_fwSimplifier) {
    _fwSimplifier->detach();
  }
  if(_bwSimplifier) {
    _bwSimplifier->detach();
  }

  delete _unprocessed;
  delete _active;
}

bool SaturationAlgorithm::forwardSimplify(Clause* c)
{
  CALL("SaturationAlgorithm::forwardSimplify");

  if(!getLimits()->fulfillsLimits(c)) {
    return false;
  }

  bool keep;
  ClauseIterator toAdd;
  ClauseIterator premises;
  _fwSimplifier->perform(c, keep, toAdd, premises);
  _unprocessed->addClauses(toAdd);
  return keep;
}

void SaturationAlgorithm::backwardSimplify(Clause* c)
{
  CALL("SaturationAlgorithm::backwardSimplify");

  BwSimplList::Iterator bsit(_bwSimplifiers);
  while(bsit.hasNext()) {
    BackwardSimplificationEngine* bse=bsit.next().ptr();

    BwSimplificationRecordIterator simplifications;
    ClauseIterator toAdd;
    ClauseIterator toRemove;
    bse->perform(c,simplifications);
    while(simplifications.hasNext()) {
      BwSimplificationRecord srec=simplifications.next();

      _unprocessed->addClauses(srec.replacements);

      Clause* redundant=srec.toRemove;
      switch(redundant->store()) {
      case Clause::PASSIVE:
        _passive->remove(redundant);
        break;
      case Clause::ACTIVE:
        _active->remove(redundant);
        break;
      default:
        ASSERTION_VIOLATION;
      }
    }
  }
}

void SaturationAlgorithm::activate(Clause* c)
{
  CALL("SaturationAlgorithm::activate");

  _selector->select(c);

  _active->add(c);
  ClauseIterator toAdd=_generator->generateClauses(c);
  _unprocessed->addClauses(toAdd);
}

void SaturationAlgorithm::setGeneratingInferenceEngine(GeneratingInferenceEngineSP generator)
{
  ASS(!_generator);
  _generator=generator;
  _generator->attach(this);
}
void SaturationAlgorithm::setForwardSimplificationEngine(ForwardSimplificationEngineSP fwSimplifier)
{
  ASS(!_fwSimplifier);
  _fwSimplifier=fwSimplifier;
  _fwSimplifier->attach(this);
}

void SaturationAlgorithm::addFrontBackwardSimplifier(BackwardSimplificationEngineSP bwSimplifier)
{
  ASS(!_bwSimplifier);
  BwSimplList::push(bwSimplifier, _bwSimplifiers);
  bwSimplifier->attach(this);
}
