/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
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
#include "Lib/Int.hpp"

namespace Saturation
{
using namespace Lib;
using namespace Kernel;

int computeLCM(int a, int b) {
  return (a*b)/Int::gcd(a, b);
}

PredicateSplitPassiveClauseContainer::PredicateSplitPassiveClauseContainer(bool isOutermost, const Shell::Options& opt, vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues, Lib::vvector<float> cutoffs, Lib::vvector<int> ratios, bool layeredArrangement)
  : PassiveClauseContainer(isOutermost, opt, name), _queues(std::move(queues)), _cutoffs(cutoffs), _ratios(), _balances(), _layeredArrangement(layeredArrangement), _simulationBalances()
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

unsigned PredicateSplitPassiveClauseContainer::bestQueue(float featureValue) const
{
  CALL("PredicateSplitPassiveClauseContainer::bestQueue");

  // compute best queue clause should be placed in
  ASS(_cutoffs.back() == std::numeric_limits<float>::max());
  for (unsigned i = 0; i < _cutoffs.size(); i++)
  {
    if (featureValue <= _cutoffs[i])
    {
      return i;
    }
  }
  // unreachable
  ASSERTION_VIOLATION;
}

void PredicateSplitPassiveClauseContainer::add(Clause* cl)
{
  CALL("PredicateSplitPassiveClauseContainer::add");
  ASS(cl->store() == Clause::PASSIVE);

  auto bestQueueIndex = bestQueue(evaluateFeature(cl));
  if (_layeredArrangement)
  {
    // add clause to all queues starting from best queue for clause
    for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
    {
      _queues[i]->add(cl);
    }
  }
  else
  {
    // add clause to best queue for clause
    _queues[bestQueueIndex]->add(cl);
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
  auto bestQueueIndex = bestQueue(evaluateFeature(cl));

  if (_layeredArrangement)
  {
    // remove clause from all queues starting from best queue for clause
    for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
    {
      _queues[i]->remove(cl);
    }
  }
  else
  {
    // remove clause from best queue for clause
    _queues[bestQueueIndex]->remove(cl);
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
  CALL("PredicateSplitPassiveClauseContainer::isEmpty");
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
  CALL("PredicateSplitPassiveClauseContainer::sizeEstimate");
  ASS(!_queues.empty());

  if (_layeredArrangement)
  {
    // Note: If we use LRS, we lose the invariant that the last queue contains all clauses (since it can have stronger limits than the other queues).
    //       as a consequence the size of the last queue is only an estimate on the size.
    return _queues.back()->sizeEstimate();
  }
  else
  {
    unsigned sum = 0;
    for (const auto& queue : _queues)
    {
      sum += queue->sizeEstimate();
    }
    return sum;
  }
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
  // this succeeds in a multi-split-queue-non-LRS-setting where we have the invariant that each clause from queue i is contained in queue j if i<j
  auto currIndex = queueIndex;
  while (currIndex < (long int)_queues.size() && _queues[currIndex]->isEmpty())
  {
    currIndex++;
  }
  // for tammet-style-queues or in the presence of LRS, we need to also consider the queues to the left as additional fallback (using the invar: at least one queue has at least one clause if popSelected is called)
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

  // note: for a non-layered arrangement, the clause only occured in _queues[currIndex] (from which it was just removed using popSelected(), so we don't need any additional clause-removal
  if (_layeredArrangement)
  {
    // remove clause from all queues
    for (unsigned i = 0; i < _queues.size(); i++)
    {
      _queues[i]->remove(cl);
    }
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
  //  this succeeds in a multi-split-queue-non-LRS-setting where we have the invariant that each clause from queue i is contained in queue j if i<j
  auto currIndex = queueIndex;
  while (currIndex < (long int)_queues.size() && !_queues[currIndex]->simulationHasNext())
  {
    currIndex++;
  }
  // for tammet-style-queues or in the presence of LRS, we need to also consider the queues to the left as additional fallback (using the invar: at least one queue has at least one clause if popSelected is called)
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
  CALL("PredicateSplitPassiveClauseContainer::ageLimited");
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
  CALL("PredicateSplitPassiveClauseContainer::weightLimited");
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
  CALL("PredicateSplitPassiveClauseContainer::fulfilsAgeLimit(Clause*)");
  auto bestQueueIndex = bestQueue(evaluateFeature(cl));
  if (_layeredArrangement)
  {
    for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
    {
      auto& queue = _queues[i];
      if (queue->fulfilsAgeLimit(cl))
      {
        return true;
      }
    }
    return false;
  }
  else
  {
    return _queues[bestQueueIndex]->fulfilsAgeLimit(cl);
  }
}

// returns true if the cl fulfills at least one age-limit of a queue it is in
// note: w here denotes the weight as returned by weight().
// this method internally takes care of computing the corresponding weightForClauseSelection.
bool PredicateSplitPassiveClauseContainer::fulfilsAgeLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("PredicateSplitPassiveClauseContainer::fulfilsAgeLimit(unsigned, unsigned, const Inference&)");
  auto bestQueueIndex = bestQueue(evaluateFeatureEstimate(numPositiveLiterals, inference));
  // note: even for non-layered-arrangements, we need to go through all queues, since the values for age, w, ... are only lower bounds (in the sense that the actual value could lead to a worse bestQueueIndex)
  for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
  {
    auto& queue = _queues[i];

    if (queue->fulfilsAgeLimit(w, numPositiveLiterals, inference))
    {
      return true;
    }
  }
  return false;
}

// returns true if the cl fulfills at least one weight-limit of a queue it is in
bool PredicateSplitPassiveClauseContainer::fulfilsWeightLimit(Clause* cl) const
{
  CALL("PredicateSplitPassiveClauseContainer::fulfilsWeightLimit(Clause*)");
  auto bestQueueIndex = bestQueue(evaluateFeature(cl));
  if (_layeredArrangement)
  {
    for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
    {
      auto& queue = _queues[i];
      if (queue->fulfilsWeightLimit(cl))
      {
        return true;
      }
    }
    return false;
  }
  else
  {
    return _queues[bestQueueIndex]->fulfilsWeightLimit(cl);
  }
}

// returns true if the cl fulfills at least one weight-limit of a queue it is in
// note: w here denotes the weight as returned by weight().
// this method internally takes care of computing the corresponding weightForClauseSelection.

bool PredicateSplitPassiveClauseContainer::fulfilsWeightLimit(unsigned w, unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("PredicateSplitPassiveClauseContainer::fulfilsWeightLimit(unsigned, unsigned, const Inference&)");
  auto bestQueueIndex = bestQueue(evaluateFeatureEstimate(numPositiveLiterals, inference));
  // note: even for non-layered-arrangements, we need to go through all queues, since the values for age, w, ... are only lower bounds (in the sense that the actual value could lead to a worse bestQueueIndex)
  for (unsigned i = bestQueueIndex; i < _queues.size(); i++)
  {
    auto& queue = _queues[i];
    if (queue->fulfilsWeightLimit(w, numPositiveLiterals, inference))
    {
      return true;
    }
  }
  return false;
}

bool PredicateSplitPassiveClauseContainer::childrenPotentiallyFulfilLimits(Clause* cl, unsigned upperBoundNumSelLits) const 
{
  CALL("PredicateSplitPassiveClauseContainer::childrenPotentiallyFulfilLimits");
  // can't conclude any lower bounds on niceness of child-clause, so have to assume that it is potentially added to all queues.
  // In particular we need to check whether at least one of the queues could potentially select children of the clause.
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
PredicateSplitPassiveClauseContainer(isOutermost, opt, name, std::move(queues), opt.theorySplitQueueCutoffs(), opt.theorySplitQueueRatios(), opt.theorySplitQueueLayeredArrangement()) {}

float TheoryMultiSplitPassiveClauseContainer::evaluateFeature(Clause* cl) const
{
  CALL("TheoryMultiSplitPassiveClauseContainer::evaluateFeature");
  // heuristically compute likeliness that clause occurs in proof
  auto inference = cl->inference();
  auto expectedRatioDenominator = _opt.theorySplitQueueExpectedRatioDenom();
  return inference.th_ancestors * expectedRatioDenominator - inference.all_ancestors;
}

float TheoryMultiSplitPassiveClauseContainer::evaluateFeatureEstimate(unsigned, const Inference& inf) const
{
  CALL("TheoryMultiSplitPassiveClauseContainer::evaluateFeatureEstimate");
  // heuristically compute likeliness that clause occurs in proof
  static int expectedRatioDenominator = _opt.theorySplitQueueExpectedRatioDenom();
  return inf.th_ancestors * expectedRatioDenominator - inf.all_ancestors;
}

AvatarMultiSplitPassiveClauseContainer::AvatarMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues) :
PredicateSplitPassiveClauseContainer(isOutermost, opt, name, std::move(queues), opt.avatarSplitQueueCutoffs(), opt.avatarSplitQueueRatios(), opt.avatarSplitQueueLayeredArrangement()) {}

float AvatarMultiSplitPassiveClauseContainer::evaluateFeature(Clause* cl) const
{
  CALL("AvatarMultiSplitPassiveClauseContainer::evaluateFeature");
  // heuristically compute likeliness that clause occurs in proof
  auto inf = cl->inference();
  return (inf.splits() == nullptr) ? 0 : inf.splits()->size();
}

float AvatarMultiSplitPassiveClauseContainer::evaluateFeatureEstimate(unsigned, const Inference& inf) const
{
  CALL("AvatarMultiSplitPassiveClauseContainer::evaluateFeatureEstimate");
  // heuristically compute likeliness that clause occurs in proof
  return (inf.splits() == nullptr) ? 0 : inf.splits()->size();
}

SineLevelMultiSplitPassiveClauseContainer::SineLevelMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues) :
PredicateSplitPassiveClauseContainer(isOutermost, opt, name, std::move(queues), opt.sineLevelSplitQueueCutoffs(), opt.sineLevelSplitQueueRatios(), opt.sineLevelSplitQueueLayeredArrangement()) {}

float SineLevelMultiSplitPassiveClauseContainer::evaluateFeature(Clause* cl) const
{
  CALL("SineLevelMultiSplitPassiveClauseContainer::evaluateFeature");
  // heuristically compute likeliness that clause occurs in proof
  return cl->getSineLevel();
}

float SineLevelMultiSplitPassiveClauseContainer::evaluateFeatureEstimate(unsigned, const Inference& inf) const
{
  CALL("SineLevelMultiSplitPassiveClauseContainer::evaluateFeatureEstimate");
  // heuristically compute likeliness that clause occurs in proof
  return inf.getSineLevel();
}

PositiveLiteralMultiSplitPassiveClauseContainer::PositiveLiteralMultiSplitPassiveClauseContainer(bool isOutermost, const Shell::Options &opt, Lib::vstring name, Lib::vvector<std::unique_ptr<PassiveClauseContainer>> queues) :
PredicateSplitPassiveClauseContainer(isOutermost, opt, name, std::move(queues), opt.positiveLiteralSplitQueueCutoffs(), opt.positiveLiteralSplitQueueRatios(), opt.positiveLiteralSplitQueueLayeredArrangement()) {}

float PositiveLiteralMultiSplitPassiveClauseContainer::evaluateFeature(Clause* cl) const
{
  CALL("PositiveLiteralMultiSplitPassiveClauseContainer::evaluateFeature");
  // heuristically compute likeliness that clause occurs in proof
  return cl->numPositiveLiterals();
}

float PositiveLiteralMultiSplitPassiveClauseContainer::evaluateFeatureEstimate(unsigned numPositiveLiterals, const Inference& inference) const
{
  CALL("PositiveLiteralMultiSplitPassiveClauseContainer::evaluateFeatureEstimate");
  return numPositiveLiterals;
}

};
