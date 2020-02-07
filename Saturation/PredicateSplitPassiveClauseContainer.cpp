/*
 * File PredicateSplitPassiveClauseContainer.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */

#include "PredicateSplitPassiveClauseContainer.hpp"

#include <numeric>
#include <string>
#include <algorithm>
#include <iterator>
#include <limits>

#include "Shell/Options.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"
#include "Lib/SharedSet.hpp"

namespace Saturation
{
using namespace Lib;
using namespace Kernel;

int computeGCD(int a, int b) {
    if (a == 0) {
      return b;
    }
    return computeGCD(b % a, a);
}
int computeLCM(int a, int b) {
  return (a*b)/computeGCD(a, b);
}

PredicateSplitPassiveClauseContainer::PredicateSplitPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues, Lib::vvector<float> cutoffs, Lib::vvector<int> ratios)
  : PassiveClauseContainer(isOutermost, opt, name), _queues(std::move(queues)), _cutoffs(cutoffs), _ratios(), _balances(), _simulationBalances()
{
  CALL("PredicateSplitPassiveClauseContainer::PredicateSplitPassiveClauseContainer");

  // sanity checks
  if (ratios.size() != _queues.size()) {
    USER_ERROR("Queue " + name + ": The number of ratios needs to match the number of queues, but " + Int::toString(ratios.size()) + " != " + Int::toString(_queues.size()));
  }
  if (_cutoffs.size() != _queues.size()) {
    USER_ERROR("Queue " + name + ": The number of cutoffs needs to match the number of queues, but " + Int::toString(_cutoffs.size()) + " != " + Int::toString(_queues.size()));
  }

  // compute lcm, which will be used to compute reverse ratios
  auto lcm = 1;
  for (unsigned i = 0; i < ratios.size(); i++)
  {
    lcm = computeLCM(lcm, ratios[i]);
  }

  // initialize
  for (unsigned i = 0; i < ratios.size(); i++)
  {
    _ratios.push_back(lcm / ratios[i]);
    _balances.push_back(0);
  }
}

PredicateSplitPassiveClauseContainer::~PredicateSplitPassiveClauseContainer() {
  CALL("PredicateSplitPassiveClauseContainer::~PredicateSplitPassiveClauseContainer");
}

unsigned PredicateSplitPassiveClauseContainer::bestQueueHeuristics(Inference* inf) const {
  auto featureValue = evaluateFeature(inf);

  // compute best queue clause should be placed in
  ASS(_cutoffs.back() == std::numeric_limits<float>::max());
  for (unsigned i = 0; i < _cutoffs.size(); i++)
  {
    if (featureValue <= _cutoffs[i])
    {
      return i;
    }
  }
  ASS(false); // unreachable
}

void PredicateSplitPassiveClauseContainer::add(Clause* cl)
{
  CALL("PredicateSplitPassiveClauseContainer::add");
  ASS(cl->store() == Clause::PASSIVE);

  // add clause to all queues starting from best queue for clause
  auto bestQueueIndex = bestQueueHeuristics(cl->inference());
  for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
  {
    _queues[i]->add(cl);
  }

  if (_isOutermost)
  {
    addedEvent.fire(cl);
  }

  ASS(cl->store() == Clause::PASSIVE);
}

void PredicateSplitPassiveClauseContainer::remove(Clause* cl)
{
  CALL("PredicateSplitPassiveClauseContainer::remove");
  if (_isOutermost)
  {
    ASS(cl->store()==Clause::PASSIVE);
  }
  // remove clause from all queues starting from best queue for clause
  auto bestQueueIndex = bestQueueHeuristics(cl->inference());
  for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
  {
    _queues[i]->remove(cl);
  }

  if (_isOutermost)
  {
    ASS(cl->store()==Clause::PASSIVE);
    removedEvent.fire(cl);
    ASS(cl->store() != Clause::PASSIVE);
  }
}

bool PredicateSplitPassiveClauseContainer::isEmpty() const
{ 
  for (const auto& queue : _queues)
  {
    if (!queue->isEmpty())
    {
      return false;
    }
  }
  return true;
}

unsigned PredicateSplitPassiveClauseContainer::sizeEstimate() const
{ 
  ASS(!_queues.empty()); 
  // Note: If we use LRS, we lose the invariant that the last queue contains all clauses (since it can have stronger limits than the other queues).
  //       as a consequence the size of the last queue is only an estimate on the size.
  return _queues.back()->sizeEstimate();
}

Clause* PredicateSplitPassiveClauseContainer::popSelected()
{
  CALL("PredicateSplitPassiveClauseContainer::popSelected");
  // compute queue from which we will pick a clause:
  // choose queue using weighted round robin
  auto minElementIt = std::min_element(_balances.begin(), _balances.end());
  auto minElement = *minElementIt; // need to save the value of the min element before updating it to a new value, since it may not remain the minimal element after the update

  auto queueIndex = std::distance(_balances.begin(), minElementIt);

  _balances[queueIndex] += _ratios[queueIndex];
  for (auto& balance : _balances)
  {
    balance -= minElement;
  }

  // if chosen queue is empty, use the next queue to the right
  // this succeeds in a non LRS-setting where we have the invariant that each clause from queue i is contained in queue j if i<j
  auto currIndex = queueIndex;
  while (currIndex < (long int)_queues.size() && _queues[currIndex]->isEmpty())
  {
    currIndex++;
  }
  // in the presence of LRS, we need to also consider the queues to the left as additional fallback (using the invar: at least one queue has at least one clause if popSelected is called)
  if (currIndex == (long int)_queues.size())
  {
    // fallback: try remaining queues, at least one of them must be nonempty
    ASS(queueIndex > 0); // otherwise we would already have searched through all queues
    currIndex = queueIndex - 1;
    while (_queues[currIndex]->isEmpty())
    {
      currIndex--;
      ASS(currIndex >= 0);
    }
  }
  ASS(!_queues[currIndex]->isEmpty());

  // pop clause from selected queue
  auto cl = _queues[currIndex]->popSelected();
  ASS(cl->store() == Clause::PASSIVE);

  // remove clause from all queues
  for (unsigned i = 0; i < _queues.size(); i++)
  {
    _queues[i]->remove(cl);
  }

  selectedEvent.fire(cl);

  return cl;
}

void PredicateSplitPassiveClauseContainer::simulationInit()
{
  CALL("PredicateSplitPassiveClauseContainer::simulationInit");

  _simulationBalances.clear();
  for (const auto& balance : _balances)
  {
    _simulationBalances.push_back(balance);
  }

  for (const auto& queue : _queues)
  {
    queue->simulationInit();
  }
}

bool PredicateSplitPassiveClauseContainer::simulationHasNext()
{
  CALL("PredicateSplitPassiveClauseContainer::simulationHasNext");
  bool hasNext = false;
  for (const auto& queue : _queues)
  {
    bool currHasNext = queue->simulationHasNext();
    hasNext = hasNext || currHasNext;
  }
  return hasNext;
}

void PredicateSplitPassiveClauseContainer::simulationPopSelected()
{
  CALL("PredicateSplitPassiveClauseContainer::simulationPopSelected");
  // compute queue from which we will pick a clause:
  // choose queue using weighted round robin
  auto minElementIt = std::min_element(_simulationBalances.begin(), _simulationBalances.end());
  auto minElement = *minElementIt; // need to save the value of the min element before updating it to a new value, since it may not remain the minimal element after the update

  auto queueIndex = std::distance(_simulationBalances.begin(), minElementIt);
  _simulationBalances[queueIndex] += _ratios[queueIndex];
  for (auto& balance : _simulationBalances)
  {
    balance -= minElement;
  }

  // if chosen queue is empty, use the next queue to the right
  // this succeeds in a non LRS-setting where we have the invariant that each clause from queue i is contained in queue j if i<j
  auto currIndex = queueIndex;
  while (currIndex < (long int)_queues.size() && !_queues[currIndex]->simulationHasNext())
  {
    currIndex++;
  }
  // in the presence of LRS, we need to also consider the queues to the left as additional fallback (using the invar: at least one queue has at least one clause if popSelected is called)
  if (currIndex == (long int)_queues.size())
  {
    // fallback: try remaining queues, at least one of them must be nonempty
    ASS(queueIndex > 0); // otherwise we would already have searched through all queues
    currIndex = queueIndex - 1;
    while (!_queues[currIndex]->simulationHasNext())
    {
      currIndex--;
      ASS(currIndex >= 0);
    }
  }

  _queues[currIndex]->simulationPopSelected();
}

// returns whether at least one of the limits was tightened
bool PredicateSplitPassiveClauseContainer::setLimitsToMax()
{
  CALL("PredicateSplitPassiveClauseContainer::setLimitsToMax");
  bool tightened = false;
  for (const auto& queue : _queues)
  {
    bool currTightened = queue->setLimitsToMax();
    tightened = tightened || currTightened;
  }
  return tightened;
}

// returns whether at least one of the limits was tightened
bool PredicateSplitPassiveClauseContainer::setLimitsFromSimulation()
{
  CALL("PredicateSplitPassiveClauseContainer::setLimitsFromSimulation");
  bool tightened = false;
  for (const auto& queue : _queues)
  {
    bool currTightened = queue->setLimitsFromSimulation();
    tightened = tightened || currTightened;
  }
  return tightened;
}

void PredicateSplitPassiveClauseContainer::onLimitsUpdated()
{
  CALL("PredicateSplitPassiveClauseContainer::onLimitsUpdated");
  for (const auto& queue : _queues)
  {
    queue->onLimitsUpdated();
  }
}

bool PredicateSplitPassiveClauseContainer::ageLimited() const
{
  for (const auto& queue : _queues)
  {
    if (queue->ageLimited())
    {
      return true;
    }
  }
  return false;
}

bool PredicateSplitPassiveClauseContainer::weightLimited() const
{
  for (const auto& queue : _queues)
  {
    if (queue->weightLimited())
    {
      return true;
    }
  }
  return false;
}

// returns true if the cl fulfils at least one age-limit of a queue it is in
bool PredicateSplitPassiveClauseContainer::fulfilsAgeLimit(Clause* cl) const
{
  for (unsigned i = bestQueueHeuristics(cl->inference()); i < _queues.size(); i++)
  {
    auto& queue = _queues[i];
    if (queue->fulfilsAgeLimit(cl))
    {
      return true;
    }
  }
  return false;
}

// returns true if the cl fulfils at least one age-limit of a queue it is in
// note: w here denotes the weight as returned by weight().
// this method internally takes care of computing the corresponding weightForClauseSelection.
bool PredicateSplitPassiveClauseContainer::fulfilsAgeLimit(unsigned age, unsigned w, unsigned numeralWeight, bool derivedFromGoal, Inference* inference) const
{
  for (unsigned i = bestQueueHeuristics(inference); i < _queues.size(); i++)
  {
    auto& queue = _queues[i];
    if (queue->fulfilsAgeLimit(age, w, numeralWeight, derivedFromGoal, inference))
    {
      return true;
    }
  }
  return false;
}

// returns true if the cl fulfils at least one weight-limit of a queue it is in
bool PredicateSplitPassiveClauseContainer::fulfilsWeightLimit(Clause* cl) const
{
  for (unsigned i = bestQueueHeuristics(cl->inference()); i < _queues.size(); i++)
  {
    auto& queue = _queues[i];
    if (queue->fulfilsWeightLimit(cl))
    {
      return true;
    }
  }
  return false;
}
// returns true if the cl fulfils at least one weight-limit of a queue it is in
// note: w here denotes the weight as returned by weight().
// this method internally takes care of computing the corresponding weightForClauseSelection.
bool PredicateSplitPassiveClauseContainer::fulfilsWeightLimit(unsigned w, unsigned numeralWeight, bool derivedFromGoal, unsigned age, Inference* inference) const
{
  for (unsigned i = bestQueueHeuristics(inference); i < _queues.size(); i++)
  {
    auto& queue = _queues[i];
    if (queue->fulfilsWeightLimit(w, numeralWeight, derivedFromGoal, age, inference))
    {
      return true;
    }
  }
  return false;
}

bool PredicateSplitPassiveClauseContainer::childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const 
{
  // can't conlude any lower bounds on niceness of child-clause, so have to assume that it is potentially added to all queues.
  // In particular we need to check whether at least one of the queues could potentially select childrens of the clause.
  for (const auto& queue : _queues)
  {
    if (queue->childrenPotentiallyFulfilLimits(cl, upperBoundNumSelLits))
    {
      return true;
    }
  }
  return false;
}

TheoryMultiSplitPassiveClauseContainer::TheoryMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues) :
PredicateSplitPassiveClauseContainer(isOutermost, opt, name, std::move(queues), opt.theorySplitQueueCutoffs(), opt.theorySplitQueueRatios()) {}

float TheoryMultiSplitPassiveClauseContainer::evaluateFeature(Inference* inf) const
{
    // heuristically compute likeliness that clause occurs in proof
    auto expectedRatioDenominator = _opt.theorySplitQueueExpectedRatioDenom();
    return inf->th_ancestors * expectedRatioDenominator - inf->all_ancestors;
}

AvatarMultiSplitPassiveClauseContainer::AvatarMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues) :
PredicateSplitPassiveClauseContainer(isOutermost, opt, name, std::move(queues), opt.avatarSplitQueueCutoffs(), opt.avatarSplitQueueRatios()) {}

float AvatarMultiSplitPassiveClauseContainer::evaluateFeature(Inference* inf) const
{
    // heuristically compute likeliness that clause occurs in proof
    return (inf->splits() == nullptr) ? 0 : inf->splits()->size();
}

};
