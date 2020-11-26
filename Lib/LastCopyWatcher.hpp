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
 * @file LastCopyWatcher.hpp
 * Defines class LastCopyWatcher.
 */


#ifndef __LastCopyWatcher__
#define __LastCopyWatcher__

#include "Debug/Assertion.hpp"

namespace Lib {

/**
 * Objects of this class are able to tell if they're the last copy of
 * the original object or not. This is basically what ReferenceCounter
 * does, just these object's don't require allocating any extra memory
 * for the counter.
 *
 * This is done by arranging objects into a cyclic two-way list of all
 * copies.
 */
class LastCopyWatcher
{
public:
  LastCopyWatcher()
  {
    _next=_previous=this;
  }
  LastCopyWatcher(const LastCopyWatcher& obj)
  {
    connect(&obj);
  }
  ~LastCopyWatcher()
  {
    disconnect();
  }
  LastCopyWatcher& operator=(const LastCopyWatcher& obj)
  {
    disconnect();
    connect(&obj);
    return *this;
  }
  bool isLast()
  {
    return this==_next;
  }
private:
  void disconnect()
  {
    _next->_previous=_previous;
    _previous->_next=_next;
  }

  void connect(const LastCopyWatcher* obj)
  {
    ASS_EQ(obj->_next->_previous, obj);

    _next=obj->_next;
    _previous=obj;

    _next->_previous=this;
    obj->_next=this;
  }

  mutable const LastCopyWatcher* _next;
  mutable const LastCopyWatcher* _previous;
};

};

#endif /* __LastCopyWatcher__ */
