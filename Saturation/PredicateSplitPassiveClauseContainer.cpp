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

#include "Shell/Options.hpp"
#include "Kernel/Clause.hpp"

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

PredicateSplitPassiveClauseContainer::PredicateSplitPassiveClauseContainer(bool isOutermost, const Options& opt) : PassiveClauseContainer(isOutermost), _opt(opt), _queues()
{
  CALL("PredicateSplitPassiveClauseContainer::PredicateSplitPassiveClauseContainer");

  // parse input-ratios
  vstringstream inputRatiosStream(_opt.splitQueueRatios());
  Lib::vvector<int> inputRatios;
  std::string currentRatio; 
  while (std::getline(inputRatiosStream, currentRatio, ','))
  {
    inputRatios.push_back(std::stoi(currentRatio));
  }

  // parse cutoffs
  vstringstream cutoffsStream(_opt.splitQueueCutoffs());
  std::string currentCutoff; 
  while (std::getline(cutoffsStream, currentCutoff, ','))
  {
    _cutoffs.push_back(std::stof(currentCutoff));
  }

  // sanity checks for ratios and cutoffs
  if (inputRatios.size() < 2) {
    USER_ERROR("Wrong usage of option '-sqr'. Needs to have at least two values (e.g. '10,1')");
  }
  if (inputRatios.size() != _cutoffs.size()) {
    USER_ERROR("The number of input ratios (supplied by option '-sqr') needs to match the number of cutoffs (supplied by option '-sqc')");
  }
  for (unsigned i = 0; i < inputRatios.size(); i++)
  {
    auto v = inputRatios[i];
    auto cutoff = _cutoffs[i];

    if(v <= 0) {
      USER_ERROR("Each ratio (supplied by option '-sqr') needs to be a positive integer");
    }
    if(! (0.0 <= cutoff && cutoff <= 1.0)) {
      USER_ERROR("Each cutoff value (supplied by option '-sqc') needs to be a float in the interval [0.0,1.0]");
    }
    if (i > 0 && cutoff <= _cutoffs[i-1])
    {
      USER_ERROR("The cutoff values (supplied by option '-sqc') must be strictly increasing");
    }
  }
  if (_cutoffs.back() != 1.0)
  {
      USER_ERROR("The last cutoff value (supplied by option '-sqc') must be 1.0");
  }

  // compute lcm, which will be used to compute reverse ratios
  auto lcm = 1;
  for (unsigned i = 0; i < inputRatios.size(); i++)
  {
    lcm = computeLCM(lcm, inputRatios[i]);
  }

  // initialize
  for (auto v : inputRatios)
  {
    _queues.push_back(Lib::make_unique<AWPassiveClauseContainer>(false, opt));
    _ratios.push_back(lcm / v);
    _balances.push_back(0);
  }
}

PredicateSplitPassiveClauseContainer::~PredicateSplitPassiveClauseContainer() {
  CALL("PredicateSplitPassiveClauseContainer::~PredicateSplitPassiveClauseContainer");

  if (_isOutermost)
  {
    auto clauseIterator = _queues.back()->iterator();
    while (clauseIterator.hasNext()) {
      Clause* cl = clauseIterator.next();
      ASS(cl->store()==Clause::PASSIVE);
      cl->setStore(Clause::NONE);
    }
  }
}

unsigned PredicateSplitPassiveClauseContainer::bestQueueHeuristics(Clause* cl) {
  // heuristically compute likeliness that clause occurs in proof
  float th_ancestors = cl->inference()->th_ancestors;
  float all_ancestors = cl->inference()->all_ancestors;
  auto theoryRatio = th_ancestors / all_ancestors;
  auto niceness = theoryRatio;

  if (_opt.splitQueueFadeIn())
  {
    if (th_ancestors <= 2.0)
    {
      niceness = 0.0;
    }
    else if (th_ancestors == 3.0 && all_ancestors <= 6.0)
    {
      niceness = 0.5;
    }
    else if (th_ancestors == 4.0 && all_ancestors <= 5.0)
    {
      niceness = 0.8;
    }
  }
  
  // compute best queue clause should be placed in
  ASS(0.0 <= niceness && niceness <= 1.0);
  ASS(_cutoffs.back() == 1.0);
  for (unsigned i = 0; i < _cutoffs.size(); i++)
  {
    if (niceness <= _cutoffs[i])
    {
      return i;
    }
  }
}

void PredicateSplitPassiveClauseContainer::add(Clause* cl)
{
  CALL("PredicateSplitPassiveClauseContainer::add");
  ASS(cl->store() == Clause::PASSIVE);

  // add clause to all queues starting from best queue for clause
  auto bestQueueIndex = bestQueueHeuristics(cl);
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
  auto bestQueueIndex = bestQueueHeuristics(cl);
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

Clause* PredicateSplitPassiveClauseContainer::popSelected()
{
  CALL("PredicateSplitPassiveClauseContainer::popSelected");
  // compute queue from which we will pick a clause:
  // choose queue using weighted round robin
  auto queueIndex = std::distance(_balances.begin(), std::min_element(_balances.begin(), _balances.end()));
  _balances[queueIndex] += _ratios[queueIndex];

  // if chosen queue is empty, use the next queue to the right
  // (note that each clause from queue i is contained in queue j if i<j)
  while (_queues[queueIndex]->isEmpty())
  {
    queueIndex++;
    ASS(queueIndex < (long int)_queues.size()); // INVAR: at least the last queue will contain a clause, otherwise popSelected would not have been called.
  }

  // pop clause from selected queue
  auto cl = _queues[queueIndex]->popSelected();
  ASS(cl->store() == Clause::PASSIVE);

  // remove clause from all queues
  for (unsigned i = 0; i < _queues.size(); i++)
  {
    _queues[i]->remove(cl);
  }

  selectedEvent.fire(cl);

  return cl;
}

ClauseIterator PredicateSplitPassiveClauseContainer::iterator()
{
  CALL("PredicateSplitPassiveClauseContainer::iterator");

  // TODO: why do we need pvi here?
  return pvi(_queues.back()->iterator());
}

};
