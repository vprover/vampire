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
 * @file Event.cpp
 * Implementing classes for handling events.
 */

#include "Event.hpp"

using namespace Lib;

SubscriptionObject::~SubscriptionObject()
{
  if(hs!=0) {
    hs->sObj=0;
  }
}

void SubscriptionObject::unsubscribe()
{
  if(hs!=0) {
    event->unsubscribe(hs);
    ASS(hs==0);
  }
}

bool SubscriptionObject::belongsTo(BaseEvent& evt)
{
  return &evt==event;
}


SubscriptionData BaseEvent::subscribe(HandlerStruct* h)
{
  HandlerList::push(h, _handlers);
  SubscriptionObject* res=new SubscriptionObject(this, h);
  h->sObj=res;
  return SubscriptionData(res);
}

void BaseEvent::unsubscribe(HandlerStruct* h)
{
  ASS(HandlerList::member(h, _handlers));
  _handlers = HandlerList::remove(h, _handlers);
  if(h->sObj) {
    h->sObj->hs=0;
  }
  delete h;
}
