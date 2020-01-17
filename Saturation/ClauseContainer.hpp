
/*
 * File ClauseContainer.hpp.
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
/**
 * @file ClauseContainer.hpp
 * Defines class ClauseContainer
 *
 */

#ifndef __ClauseContainer__
#define __ClauseContainer__

#include "Forwards.hpp"

#include "Lib/Event.hpp"
#include "Lib/VirtualIterator.hpp"
#include "Lib/Deque.hpp"
#include "Lib/Stack.hpp"

#include "Lib/Allocator.hpp"

#include "Limits.hpp"

#define OUTPUT_LRS_DETAILS 0

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

class ClauseContainer
{
public:
  CLASS_NAME(ClauseContainer);
  USE_ALLOCATOR(ClauseContainer);

  virtual ~ClauseContainer() {}
  ClauseEvent addedEvent;
  /**
   * This event fires when a clause is removed from the
   * container because it is no longer needed, e.g. it was
   * backward-simplified, or the container is destroyed.
   * It does not fire for clauses that are removed from the
   * container because they are selected to be further
   * processed by the saturation algorithm (e.g. activated).
   */
  ClauseEvent removedEvent;
  /**
   * This event fires when a clause is removed from the
   * container to be further processed by the saturation
   * algorithm (e.g. activated).
   */
  ClauseEvent selectedEvent;
  virtual void add(Clause* c) = 0;
  void addClauses(ClauseIterator cit);
};

class RandomAccessClauseContainer
: public ClauseContainer
{
public:
  CLASS_NAME(RandomAccessClauseContainer);
  USE_ALLOCATOR(RandomAccessClauseContainer);

  virtual void attach(SaturationAlgorithm* salg);
  virtual void detach();

  virtual unsigned size() const = 0;
  virtual void remove(Clause* c) = 0;
  void removeClauses(ClauseIterator cit);

protected:
  RandomAccessClauseContainer() :_salg(0) {}
  SaturationAlgorithm* getSaturationAlgorithm() { return _salg; }

  virtual void onLimitsUpdated() {}
private:
  SaturationAlgorithm* _salg;
  SubscriptionData _limitChangeSData;
};

class PlainClauseContainer : public ClauseContainer {
public:
  CLASS_NAME(PlainClauseContainer);
  USE_ALLOCATOR(PlainClauseContainer);

  virtual void add(Clause* c)
  {
    addedEvent.fire(c);
  }
};


class UnprocessedClauseContainer
: public ClauseContainer
{
public:
  CLASS_NAME(UnprocessedClauseContainer);
  USE_ALLOCATOR(UnprocessedClauseContainer);

  virtual ~UnprocessedClauseContainer();
  UnprocessedClauseContainer() : _data(64) {}
  void add(Clause* c);
  Clause* pop();
  bool isEmpty() const
  { return _data.isEmpty(); }
private:
  Deque<Clause*> _data;
};

class PassiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  CLASS_NAME(PassiveClauseContainer);
  USE_ALLOCATOR(PassiveClauseContainer);

  PassiveClauseContainer(bool isOutermost) : _isOutermost(isOutermost) {}
  virtual ~PassiveClauseContainer(){};

  virtual bool isEmpty() const = 0;
  virtual Clause* popSelected() = 0;

  virtual ClauseIterator iterator() = 0;
  virtual unsigned size() const = 0;

  virtual Limits* getLimits() = 0;
  virtual void updateLimits(long long estReachableCnt) {}

protected:
  bool _isOutermost;
};

class ActiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  CLASS_NAME(ActiveClauseContainer);
  USE_ALLOCATOR(ActiveClauseContainer);

  ActiveClauseContainer(const Options& opt) : _size(0), _opt(opt) {}

  void add(Clause* c);
  void remove(Clause* c);

  unsigned size() const { return _size; }

protected:
  void onLimitsUpdated();
private:
  unsigned _size;
  const Options& _opt;
};


};

#endif /*__ClauseContainer__*/
