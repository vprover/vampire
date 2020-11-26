/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Event.hpp
 * Defines class Event
 *
 */

#ifndef __Event__
#define __Event__

#include "List.hpp"
#include "SmartPtr.hpp"

namespace Lib
{

class SubscriptionObject;


typedef SmartPtr<SubscriptionObject> SubscriptionData;

class BaseEvent
{
public:
  /** Return true iif there are no subscribers of this event */
  bool isEmpty()
  {
    return !_handlers;
  }
protected:
  struct HandlerStruct {
    virtual ~HandlerStruct() {}
    SubscriptionObject* sObj;
  };

  BaseEvent() : _handlers(0) {}
  ~BaseEvent()
  {
    while(_handlers) {
      unsubscribe(_handlers->head());
    }
  }

  typedef List<HandlerStruct*> HandlerList;

  SubscriptionData subscribe(HandlerStruct* h);
  void unsubscribe(HandlerStruct* h);

  HandlerList* _handlers;

  friend class SubscriptionObject;
};

class SubscriptionObject
{
public:
  SubscriptionObject(BaseEvent* evt, BaseEvent::HandlerStruct* hs)
  : event(evt), hs(hs) {}
  ~SubscriptionObject();
  void unsubscribe();
  bool belongsTo(BaseEvent& evt);

  CLASS_NAME(SubscriptionObject);
  USE_ALLOCATOR(SubscriptionObject);
private:
  BaseEvent* event;
  BaseEvent::HandlerStruct* hs;

  friend class BaseEvent;
};


class PlainEvent
: public BaseEvent
{
public:
  void fire()
  {
    HandlerList* hit=_handlers;
    while(hit) {
      static_cast<SpecificHandlerStruct*>(hit->head())->fire();
      hit=hit->tail();
    }
  }
  template<class Cls>
  SubscriptionData subscribe(Cls* obj, void (Cls::*method)())
  {
    return BaseEvent::subscribe(getHandlerStruct(obj,method));
  }
protected:
  struct SpecificHandlerStruct
  : public HandlerStruct
  {
    virtual void fire() = 0;
  };
  template<class Cls>
  struct MethodSpecificHandlerStruct
  : public SpecificHandlerStruct
  {
    Cls* pObj;
    void(Cls::*pMethod)();
    void fire()
    {
      (pObj->*pMethod)();
    }
    CLASS_NAME(PlainEvent::MethodSpecificHandlerStruct<Cls>);
    USE_ALLOCATOR(MethodSpecificHandlerStruct);
  };

  template<class Cls>
  HandlerStruct* getHandlerStruct(Cls* obj, void (Cls::*method)())
  {
    MethodSpecificHandlerStruct<Cls>* res=new MethodSpecificHandlerStruct<Cls>();
    res->pObj=obj;
    res->pMethod=method;
    return res;
  }
};

template<typename T>
class SingleParamEvent
: public BaseEvent
{
public:
  void fire(T t)
  {
    CALL("SingleParamEvent::fire");

    HandlerList* hit=_handlers;
    while(hit) {
      static_cast<SpecificHandlerStruct*>(hit->head())->fire(t);
      hit=hit->tail();
    }
  }
  template<class Cls>
  SubscriptionData subscribe(Cls* obj, void (Cls::*method)(T))
  {
    return BaseEvent::subscribe(getHandlerStruct(obj,method));
  }
protected:
  struct SpecificHandlerStruct
  : public HandlerStruct
  {
    virtual void fire(T t) = 0;
  };

  template<class Cls>
  struct MethodSpecificHandlerStruct
  : public SpecificHandlerStruct
  {
    Cls* pObj;
    void(Cls::*pMethod)(T);

    void fire(T t)
    {
      (pObj->*pMethod)(t);
    }

    CLASS_NAME(MethodSpecificHandlerStruct);
    USE_ALLOCATOR(MethodSpecificHandlerStruct);
  };

  template<class Cls>
  HandlerStruct* getHandlerStruct(Cls* obj, void (Cls::*method)(T))
  {
    MethodSpecificHandlerStruct<Cls>* res=new MethodSpecificHandlerStruct<Cls>();
    res->pObj=obj;
    res->pMethod=method;
    return res;
  }
  
 
};


template<typename T1, typename T2>
class TwoParamEvent
: public BaseEvent
{
public:
  void fire(T1 t1, T2 t2)
  {
    HandlerList* hit=_handlers;
    while(hit) {
      static_cast<SpecificHandlerStruct*>(hit->head())->fire(t1, t2);
      hit=hit->tail();
    }
  }
  template<class Cls>
  SubscriptionData subscribe(Cls* obj, void (Cls::*method)(T1, T2))
  {
    return BaseEvent::subscribe(getHandlerStruct(obj,method));
  }
protected:
  struct SpecificHandlerStruct
  : public HandlerStruct
  {
    virtual void fire(T1 t1, T2 t2) = 0;
  };

  template<class Cls>
  struct MethodSpecificHandlerStruct
  : public SpecificHandlerStruct
  {
    Cls* pObj;
    void(Cls::*pMethod)(T1,T2);

    void fire(T1 t1, T2 t2)
    {
      (pObj->*pMethod)(t1, t2);
    }

    CLASS_NAME("TwoParamEvent::MethodSpecificHandlerStruct");
    USE_ALLOCATOR(MethodSpecificHandlerStruct);
  };

  template<class Cls>
  HandlerStruct* getHandlerStruct(Cls* obj, void (Cls::*method)(T1,T2))
  {
    MethodSpecificHandlerStruct<Cls>* res=new MethodSpecificHandlerStruct<Cls>();
    res->pObj=obj;
    res->pMethod=method;
    return res;
  }
};


};

#endif /*__Event__*/
