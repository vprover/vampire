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
 * @file RatioKeeper.hpp
 * Defines class RatioKeeper.
 */

#ifndef __RatioKeeper__
#define __RatioKeeper__

#include "Forwards.hpp"

#include "Debug/Tracer.hpp"

namespace Lib {

class RatioKeeper {
public:
  RatioKeeper(int firstRatio, int secondRatio, unsigned buffer=0)
  : _firstRatio(firstRatio), _secondRatio(secondRatio), _buffer(buffer), _lastWasFirst(true), _balance(0) {}

  bool shouldDoFirst() const
  {
    return balanceFitsBuffer() ? _lastWasFirst : _balance>=0;
  }
  bool shouldDoSecond() const
  {
    return balanceFitsBuffer() ? !_lastWasFirst : _balance<0;
  }

  void doFirst(int cost=1)
  {
    CALL("RatioKeeper::doFirst");
    ASS(shouldDoFirst());
    _balance -= cost*_secondRatio;
    _lastWasFirst = true;
  }

  void doSecond(int cost=1)
  {
    CALL("RatioKeeper::doSecond");
    ASS(shouldDoSecond());
    _balance += cost*_firstRatio;
    _lastWasFirst = false;
  }

  void alwaysDoFirst()
  {
    _firstRatio = _secondRatio = 0;
    _balance = 1;
    _lastWasFirst = true;
  }
  void alwaysDoSecond()
  {
    _firstRatio = _secondRatio = 0;
    _balance = -1;
    _lastWasFirst = false;
  }
private:
  bool balanceFitsBuffer() const { return _balance<_buffer && _balance>-_buffer; }

  int _firstRatio;
  int _secondRatio;
  int _buffer;

  bool _lastWasFirst;
  int _balance;
};

}

#endif // __RatioKeeper__
