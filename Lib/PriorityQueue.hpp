#ifndef __PriorityQueue__
#define __PriorityQueue__

#include "Lib/Comparison.hpp"
#include "Lib/SkipList.hpp"

namespace Lib
{
template<typename T>
struct PriorityPair
{
  float priority;
  T data;
};

template<typename T>
class PriorityPairComparator
{
public:
  static inline Lib::Comparison compare(float key, PriorityPair<T> value)
  {
    if(key < value.priority)
    {
      return Lib::LESS;
    }
    else if(key > value.priority)
    {
      return Lib::GREATER;
    }
    else
    {
      return Lib::EQUAL;
    }
  }
};

template<typename T>
class PriorityQueue
{
public:
  void insert(float priority, T data)
  {
    auto ptr = _underlying.insertPosition(priority);
    ptr->data = data;
    ptr->priority = priority;
  }

  T pop()
  {
    return _underlying.pop().data;
  }

  bool isEmpty() const
  {
    return _underlying.isEmpty();
  }

private:
  Lib::SkipList<PriorityPair<T>, PriorityPairComparator<T>> _underlying;
};
}

#endif
