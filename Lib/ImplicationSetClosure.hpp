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
 * @file ImplicationSetClosure.hpp
 * Defines class ImplicationSetClosure.
 */

#ifndef __ImplicationSetClosure__
#define __ImplicationSetClosure__

#include "Forwards.hpp"

#include "DHSet.hpp"
#include "MapToLIFO.hpp"
#include "Stack.hpp"



namespace Lib {

/**
 * Class that accepts an initial set and implications expressing
 * that presence of one element in the set implies presence of another.
 * From this the object generates the final saturated set.
 */
template<typename T>
class ImplicationSetClosure {
private:
  typedef DHSet<T> SelSet;
  typedef MapToLIFO<T,T> ImplMap;

  SelSet _selected;
  ImplMap _implied;
public:
  void add(const T& val) {
    CALL("ImplicationSetClosure::add");

    if(_selected.contains(val)) { return; }
    static Stack<T> todo;
    todo.reset();
    todo.push(val);
    while(todo.isNonEmpty()) {
      T v = todo.pop();
      _selected.insert(v);
      typename ImplMap::ValIterator implIt = _implied.keyIterator(v);
      while(implIt.hasNext()) {
	T impl = implIt.next();
	if(_selected.contains(impl)) { continue; }
	todo.push(impl);
      }
    }
  }

  template<class It>
  void addFromIterator(It it) {
    CALL("ImplicationSetClosure::addFromIterator");

    while(it.hasNext()) {
      add(it.next());
    }
  }

  void addImplication(const T& prem, const T& conseq) {
    CALL("ImplicationSetClosure::addImplication");

    if(prem==conseq) { return; }
    _implied.pushToKey(prem, conseq);
    if(_selected.contains(prem)) {
      add(conseq);
    }
  }

  bool contains(const T& val) const {
    return _selected.contains(val);
  }

  class Iterator : public SelSet::Iterator
  {
  public:
    Iterator(const ImplicationSetClosure& parent) : DHSet<T>::Iterator(parent._selected) {}
  };
};

}

#endif // __ImplicationSetClosure__
