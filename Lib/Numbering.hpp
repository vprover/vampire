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
    unsigned* pres;
    if(_map.getValuePtr(obj, pres, _nextNum)) {
      ALWAYS(_rev.insert(_nextNum, obj));
      _nextNum++;
    }
    return *pres;
  }
  void assign(T obj, unsigned num)
  {
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
  T obj(unsigned num)
  {
    return _rev.get(num);
  }
  bool contains(T obj)
  {
    return _map.find(obj);
  }
private:
  DHMap<T, unsigned> _map;
  DHMap<unsigned, T> _rev;

  unsigned _nextNum;

};

};

#endif /* __Numbering__ */
