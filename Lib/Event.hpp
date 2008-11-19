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

//template<class Handler>
class BaseEvent
{
public:
  /** Return true iif there are no subscribers of this event */
  bool isEmpty()
  {
    return !_handlers;
  }
protected:
  BaseEvent() : _handlers(0) {}
  
  struct HandlerStruct {
    virtual ~HandlerStruct() {}
    bool operator==(const HandlerStruct& s) { return pObj==s.pObj && pMethod==s.pMethod; }
    void* pObj;
    /**
     * @warning Method pointer is converted with reinterpred_cast<void*>
     * and stored here. It's not legal by standard, but it works.  
     */
    void* pMethod;
  };
  typedef List<HandlerStruct*> HandlerList;
  
  void subscribe(HandlerStruct* h)
  {
    _handlers=new HandlerList(h, _handlers);
  }
  void unsubscribe(HandlerStruct* h)
  {
    HandlerList** hit=&_handlers;
    while(*hit) {
      if(*(*hit)->head()==*h) {
	delete (*hit)->head();
	HandlerList* lstObj=*hit;
	*hit=lstObj->tail();
	delete lstObj;
	break;
      }
      hit=&(*hit)->tailReference();
    }
    delete h;
  }

  HandlerList* _handlers;
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
  void subscribe(Cls* obj, void (Cls::*method)())
  {
    BaseEvent::subscribe(getHandlerStruct(obj,method));
  }
  template<class Cls>
  void unsubscribe(Cls* obj, void (Cls::*method)())
  {
    BaseEvent::unsubscribe(getHandlerStruct(obj,method));
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
    void fire()
    {
      (static_cast<Cls*>(pObj)->*static_cast<void(Cls::*)()>(pMethod))();
    }
  };
  
  template<class Cls>
  HandlerStruct getHandlerStruct(Cls* obj, void (Cls::*method)())
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
    HandlerList* hit=_handlers;
    while(hit) {
      static_cast<SpecificHandlerStruct*>(hit->head())->fire(t);
      hit=hit->tail();
    }
  }
  template<class Cls>
  void subscribe(Cls* obj, void (Cls::*method)(T))
  {
    BaseEvent::subscribe(getHandlerStruct(obj,method));
  }
  template<class Cls>
  void unsubscribe(Cls* obj, void (Cls::*method)(T))
  {
    BaseEvent::unsubscribe(getHandlerStruct(obj,method));
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
    void fire(T t)
    {
      Cls* obj = static_cast<Cls*>(SpecificHandlerStruct::pObj);
      void(Cls::*method)(T) = reinterpret_cast<void(Cls::*&)(T)>(SpecificHandlerStruct::pMethod); 
      (obj->*method)(t);
    }
  };
  
  template<class Cls>
  HandlerStruct* getHandlerStruct(Cls* obj, void (Cls::*method)(T))
  {
    MethodSpecificHandlerStruct<Cls>* res=new MethodSpecificHandlerStruct<Cls>();
    res->pObj=obj;
    res->pMethod=reinterpret_cast<void*&>(method);
    return res;
  }
};


};

#endif /*__Event__*/
