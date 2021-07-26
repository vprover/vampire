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
 * @file Numbering.hpp
 * Defines class Numbering.
 */


#ifndef __Numbering__
#define __Numbering__

#include "DHMap.hpp"

namespace Lib {

template<typename T, unsigned Start=0>
class Numbering
{
public:
  Numbering() : _nextNum(Start) {}
  unsigned get(T obj)
  {
    CALL("Numbering::get");
    unsigned* pres;
    if(_map.getValuePtr(obj, pres, _nextNum)) {
      ALWAYS(_rev.insert(_nextNum, obj));
      _nextNum++;
    }
    return *pres;
  }
  void assign(T obj, unsigned num)
  {
    CALL("Numbering::assign");
    if(_map.insert(obj, num)) {
      ALWAYS(_rev.insert(num, obj));
      if(num>=_nextNum) {
        _nextNum=num+1;
      }
    }
#if VDEBUG
    else {
      ASS_EQ(_map.get(obj),num);
    }
#endif
  }
  /**
   * Return a number that doesn't correspond to any object
   */
  unsigned getSpareNum()
  {
    CALL("Numbering::getSpareNum");
    return _nextNum++;
  }
  T obj(unsigned num) const
  {
    CALL("Numbering::obj");
    return _rev.get(num);
  } 
  bool findObj(unsigned num, T& res) const
  {
    return _rev.find(num, res);
  }
  bool contains(T obj) const
  {
    return _map.find(obj);
  }
  /** All numbers assigned by this object are less than or equal
   * to the result of this function */
  unsigned getNumberUpperBound() const
  {
    CALL("Numbering::getNumberUpperBound");
    return _nextNum==0 ? 0 : (_nextNum-1);
  }
  void reset(){
    _map.reset();
    _rev.reset();
    _nextNum=Start;
  }

  friend std::ostream& operator<<(std::ostream& out, Numbering const& self)
  { 
    out << "{";
    if (Start < self._nextNum) {
      out << Start << " -> " << self.obj(Start);
      for (unsigned i = Start + 1; i < self._nextNum; i++) {
        out << ", " << i << " -> " << self.obj(i);
      }
    }
    return out << "}";
  }
private:
  DHMap<T, unsigned> _map;
  DHMap<unsigned, T> _rev;

  unsigned _nextNum;
};

};

#endif /* __Numbering__ */
