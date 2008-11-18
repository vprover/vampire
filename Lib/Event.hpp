/**
 * @file Event.hpp
 * Defines class Event
 *
 */

#ifndef __Event__
#define __Event__

#include "List.hpp"

namespace Lib
{

template<class Handler>
class BaseEvent
{
public:
  void registerHandler(Handler* h)
  {
    _handlers=new HandlerList(h, _handlers);
  }
  void unregisterHandler(Handler* h)
  {
    _handlers=_handlers->remove(h);
  }
protected:
  Event() : _handlers(0) {}
  typedef List<Handler*> HandlerList;
  HandlerList* _handlers;
};

class PlainEventHandler
{
public:
  virtual ~PlainEventHandler() {}
  virtual void handle() = 0;
};

class PlainEvent
:public BaseEvent<PlainEventHandler>
{
  void fire()
  {
    HandlerList hit=_handlers;
    while(hit) {
      hit->head()->handle();
      hit=hit->tail();
    }
  }
};

template<typename T>
class SingleParamEventHandler
{
public:
  virtual ~SingleParamEventHandler() {}
  virtual void handle(T t) = 0;
};

template<typename T>
class SingleParamEvent
:public BaseEvent<SingleParamEventHandler>
{
  void fire(T t)
  {
    HandlerList hit=_handlers;
    while(hit) {
      hit->head()->handle(t);
      hit=hit->tail();
    }
  }
};


};

#endif /*__Event__*/
