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
  void doUnion(int c1, int c2);
  void finish();
  int getComponentCount() { return _components.size(); }
private:
  int root(int c);

  int _cnt;

  /**
   * Contains data about how elements are connected into components.
   *
   * Before call to the @b finish() method:
   *
   * @b _data[c] contains number of the parent element of @b c -th
   * element. If @b _data[c]==-1, c is the root element of its
   * component.
   *
   * Invariant: The root element is always the one with the
   * lowest number.

   * After call to the @b finish() method:
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
    ElementIterator(int first, int* data)
    : _next(first), _data(data) {}

    int _next;
    int* _data;

    friend class ComponentIterator;
  };
  class ComponentIterator
  {
  public:
    DECL_ELEMENT_TYPE(ElementIterator);
    ComponentIterator(IntUnionFind& obj)
    : _cit(obj._components), _data(obj._data) {}

    bool hasNext() { return _cit.hasNext(); }
    ElementIterator next() { return ElementIterator(_cit.next(), _data); }
  private:
    Stack<int>::Iterator _cit;
    int* _data;
  };
};

}

#endif /* __IntUnionFind__ */
