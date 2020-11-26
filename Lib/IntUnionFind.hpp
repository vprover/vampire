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
 * @file IntUnionFind.hpp
 * Defines class IntUnionFind implementing union-find algorithm for integers.
 */

#ifndef __IntUnionFind__
#define __IntUnionFind__

#include "Reflection.hpp"
#include "Stack.hpp"

namespace Lib {

class IntUnionFind {
public:
  IntUnionFind(int cnt);
  ~IntUnionFind();
  bool doUnion(int c1, int c2);
  int root(int c) const;
  void reset();
  void evalComponents();
  int getComponentCount();
private:

  int _cnt;

  bool _modified;

  /**
   * @b _parents[c] contains number of the parent element of @b c -th
   * element. If @b _parents[c]==-1, c is the root element of its
   * component.
   *
   * Invariant: The root element is always the one with the
   * lowest number in the component.
   *
   * Is mutable to allow path compression in the @c root function which
   * is const.
   */
  mutable int* _parents;

  /**
   * After call to the @b finish() method contains data about how
   * elements are connected into components.
   *
   * @b _data contains components in the form of linked lists.
   * @b _data[c] contains number of the next element in the same
   * component as @b c -th one, or -1 if there is no such.
   */
  int* _data;
  Stack<int> _components;

public:
  class ComponentIterator;
  class ElementIterator
  {
  public:
    DECL_ELEMENT_TYPE(int);

    bool hasNext() { return _next!=-1; }
    int next()
    {
      CALL("IntUnionFind::ElementIterator::next");
      ASS_NEQ(_next,-1);

      int res=_next;
      _next=_data[_next];
      return res;
    }
  private:
    ElementIterator(int first, const int* data)
    : _next(first), _data(data) {}

    int _next;
    const int* _data;

    friend class ComponentIterator;
  };

  /**
   * Iterator over iterators on component
   *
   * Calling the @b doUnion function does not affect the iterator
   * as long as the @b evalComponents function is not called
   */
  class ComponentIterator
  {
  public:
    DECL_ELEMENT_TYPE(ElementIterator);
    /**
     * Construct the iterator
     *
     * The @b evalComponents function must be called before
     * this constructor is called (and if the @b doUnion is called
     * later, the @b evalComponents has to be called again).
     */
    ComponentIterator(const IntUnionFind& obj)
    : _cit(obj._components), _data(obj._data)
    {
      CALL("IntUnionFind::ComponentIterator::ComponentIterator");
      ASS(!obj._modified); //the evalComponents function must have been called before
    }

    bool hasNext() { return _cit.hasNext(); }
    ElementIterator next() { return ElementIterator(_cit.next(), _data); }
  private:
    Stack<int>::ConstIterator _cit;
    const int* _data;
  };
};

}

#endif /* __IntUnionFind__ */
