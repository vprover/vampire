/**
 * @file ClauseContainer.hpp
 * Defines class ClauseContainer
 *
 */

#ifndef __ClauseContainer__
#define __ClauseContainer__

#include "../Lib/Event.hpp"
#include "../Lib/VirtualIterator.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/Forwards.hpp"

namespace Saturation
{

using namespace Lib;
using namespace Kernel;

class ClauseContainer
{
public:
  virtual ~ClauseContainer() 
  {
    //when destroying the container, all subscribrions 
    //to its events must be already canceled
    ASS(addedEvent.isEmpty());
    ASS(removedEvent.isEmpty());
  }
  ClauseEvent addedEvent;
  ClauseEvent removedEvent;
  virtual void add(Clause* c) = 0;
  virtual void addClauses(ClauseIterator cit);
};

class RandomAccessClauseContainer
: public ClauseContainer
{
  virtual void remove(Clause* c) = 0;
};

class UnprocessedClauseContainer
: public ClauseContainer
{
public:
  UnprocessedClauseContainer() : _data(64) {}
  void add(Clause* c)
  {
    _data.push(c);
    addedEvent.fire(c);
  }
  Clause* pop()
  {
    Clause* res=_data.pop();
    removedEvent.fire(res);
    return res;
  }
  bool isEmpty()
  {
    return _data.isEmpty();
  }
private:
  Stack<Clause*> _data;
};

class PassiveClauseContainer
: public RandomAccessClauseContainer
{
  virtual Clause* popSelected() = 0;
};

class ActiveClauseContainer
: public RandomAccessClauseContainer
{
  void add(Clause* c)
  {
    addedEvent.fire(c);
  }
  void remove(Clause* c)
  {
    removedEvent.fire(c);
  }
};


};

#endif /*__ClauseContainer__*/
