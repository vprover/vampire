/**
 * @file ClauseContainer.hpp
 * Defines class ClauseContainer
 *
 */

#ifndef __ClauseContainer__
#define __ClauseContainer__

#include "../Forwards.hpp"

#include "../Lib/Event.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Stack.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

class ClauseContainer
{
public:
  virtual ~ClauseContainer() {}
  ClauseEvent addedEvent;
  ClauseEvent removedEvent;
  virtual void add(Clause* c) = 0;
  void addClauses(ClauseIterator cit);
};

class RandomAccessClauseContainer
: public ClauseContainer
{
public:
  virtual void remove(Clause* c) = 0;
  void removeClauses(ClauseIterator cit);
};

class UnprocessedClauseContainer
: public ClauseContainer
{
public:
  UnprocessedClauseContainer() : _data(64) {}
  void add(Clause* c);
  Clause* pop();
  bool isEmpty() const
  { return _data.isEmpty(); }
private:
  Stack<Clause*> _data;
};

class PassiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  virtual bool isEmpty() const = 0;
  virtual Clause* popSelected() = 0;
};

class ActiveClauseContainer
: public RandomAccessClauseContainer
{
public:
  void add(Clause* c);
  void remove(Clause* c);
};


};

#endif /*__ClauseContainer__*/
