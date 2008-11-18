/**
 * @file ClauseContainer.hpp
 * Defines class ClauseContainer
 *
 */

#ifndef __ClauseContainer__
#define __ClauseContainer__

#include "../Lib/Event.hpp"
#include "../Lib/Stack.hpp"
#include "../Kernel/Forwards.hpp"

namespace Saturation
{

class ClauseContainer
{
public:
  ClauseEvent addedEvent;
  ClauseEvent removedEvent;
  virtual void add(Clause* c) = 0;
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
  void add(Clause* c)
  {
    _data.push(c);
    addedEvent.fire(c);
  }
  void pop()
  {
    Clause* res=_data.pop();
    removedEvent.fire(res);
    return res;
  }
  void isEmpty()
  {
    return _data.isEmpty();
  }
private:
  Stack<Clause*> _data;
};

class PassiveClauseContainer
: public RandomAccessClauseContainer
{
  Clause* popSelected() = 0;
};

class ActiveClauseContainer
: public RandomAccessClauseContainer
{
  
};


};

#endif /*__ClauseContainer__*/
