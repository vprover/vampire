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
 * @file Deque.hpp
 * Defines class Deque.
 */

#ifndef __Deque__
#define __Deque__

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "Reflection.hpp"

namespace Lib {

/**
 * Class of double-ended queues
 */
template<class C>
class Deque
{
private:
  //private and undefined operator= and copy constructor to avoid implicitly generated ones
  Deque(const Deque&);
  Deque& operator=(const Deque&);
public:
  class Iterator;

  DECL_ELEMENT_TYPE(C);
  DECL_ITERATOR_TYPE(Iterator);

  /**
   * Create a stack having initialCapacity.
   */
  inline
  explicit Deque (size_t initialCapacity=8)
    : _capacity(initialCapacity)
  {
    CALL("Deque::Deque");
    ASS_G(initialCapacity,1);

    void* mem = ALLOC_KNOWN(_capacity*sizeof(C),"Deque<>");
    _data = static_cast<C*>(mem);
    _front = _data;
    _back = _data;
    _end = _data+_capacity;
  }

  /** De-allocate the stack
   * @since 13/01/2008 Manchester
   */
  inline ~Deque()
  {
    CALL("Stack::~Stack");

    C* p=_back;
    while(p!=_front) {
      if(p==_data) {
	p=_end;
      }
      (--p)->~C();
    }
    DEALLOC_KNOWN(_data,_capacity*sizeof(C),"Deque<>");
  }

  /**
   * Return a reference to the n-th element of the deque
   *
   * 0-th element is the one at the front.
   */
  inline
  C& operator[](size_t n)
  {
    ASS_L(n, size());

    C* ptr=_front+n;
    if(ptr>=_end) {
      ptr-=_capacity;
    }

    return *ptr;
  }

  /**
   * Return a reference to the n-th element of the deque
   *
   * 0-th element is the one at the front.
   */
  inline
  const C& operator[](size_t n) const
  {
    return const_cast<Deque&>(*this)[n];
  }

  /**
   * Return the front of the deque
   */
  inline
  C& front() const
  {
    ASS(_front >= _data);
    ASS(_front < _end);

    return *_front;
  }

  /**
   * Set top to a new value.
   * @since 14/03/2006 Bellevue
   */
  inline
  void setFront(C elem)
  {
    CALL("Deuqe::setFront");

    front() = elem;
  }

  /**
   * True if the stack is empty.
   * @since 11/03/2006 Bellevue
   */
  inline
  bool isEmpty() const
  {
    return _front == _back;
  } // Stack::isEmpty()

  /**
   * True if the stack is non-empty.
   * @since 11/03/2006 Bellevue
   */
  inline
  bool isNonEmpty() const
  {
    return _front != _back;
  } // Stack::nonempty()

  /**
   * Push new element on the back of the deque
   */
  inline
  void push_back(C elem)
  {
    CALL("Deque::push_back");

    if(shouldExpand()) {
      expand();
    }
    ASS(_back < _end);
    new(_back) C(elem);

    _back++;
    if(_back==_end) {
      _back=_data;
    }
    ASS_NEQ(_front, _back);
  }

  /**
   * Push new element on the back of the deque
   */
  inline
  void push_front(C elem)
  {
    CALL("Deque::push_front");

    if(shouldExpand()) {
      expand();
    }

    if(_front==_data) {
      _front=_end;
    }
    _front--;

    new(_front) C(elem);

    ASS_NEQ(_front, _back);
  }

  /**
   * Pop an element from the front of the deque
   */
  inline
  C pop_front()
  {
    CALL("Deque::pop_front");
    ASS(isNonEmpty());

    C res=*_front;
    _front->~C();

    _front++;
    if(_front==_end) {
      _front=_data;
    }

    return res;
  }

   /**
   * Pop an element from the back of the deque
   */
  inline
  C& back() const
  {
    CALL("Deque::back");
    ASS(isNonEmpty());

    C* res = _back;
    if(res==_data) {
      res=_end;
    }
    res--;
    return *res;
  }

  
  /**
   * Pop an element from the back of the deque
   */
  inline
  C pop_back()
  {
    CALL("Deque::pop_back");
    ASS(isNonEmpty());

    if(_back==_data) {
      _back=_end;
    }
    _back--;

    C res=*_back;
    _back->~C();

    return res;
  }


  /** Empties the deque */
  inline
  void reset()
  {
    C* p=_back;
    while(p!=_front) {
      if(p==_data) {
	p=_end;
      }
      (--p)->~C();
    }

    _front = _data;
    _back = _data;
  }

  /**
   * Put all elements of an iterator onto the stack.
   */
  template<class It>
  void pushBackFromIterator(It it) {
    CALL("Deque::pushBackFromIterator");

    while(it.hasNext()) {
      push_back(it.next());
    }
  }

   /**
   * Put all elements of an iterator to the front of the stack.
   */
  template<class It>
  void pushFrontFromIterator(It it) {
    CALL("Deque::pushFrontFromIterator");

    while(it.hasNext()) {
      push_front(it.next());
    }
  }

  /** Return the number of elements in the deque */
  inline
  size_t size() const
  {
    if(_front>_back) {
      return (_back+_capacity) - _front;
    }
    return _back - _front;
  }

  friend class Iterator;

  /** Iterator iterates over the elements of a deque
   *  @warning The contents of the stack should not be changed by
   *           other operations when a stack is traversed using an
   *           iterator
   */
  class Iterator {
  public:
    DECL_ELEMENT_TYPE(C);
    /** create an iterator for @b d */
    inline
    explicit Iterator (Deque& d)
      : _pointer(d._front), _begin(d._data), _end(d._end), _afterLast(d._back)
    {
    }

    /** true if there exists the next element */
    inline
    bool hasNext() const
    {
      return _pointer != _afterLast;
    }

    /** return the next element */
    inline
    C next()
    {
      ASS(hasNext());
      C res=*_pointer;
      _pointer++;
      if(_pointer==_end) {
	_pointer=_begin;
      }
      return res;
    }

  private:
    C* _pointer;
    C* _begin;
    C* _end;
    C* _afterLast;
  };
  
    /**
   * Iterator iterates over the elements of a deque from front to back.
   *
   *  @warning The contents of the stack should not be changed by
   *           other operations when a stack is traversed using an
   *           iterator
   */
  class FrontToBackIterator {
  public:
    DECL_ELEMENT_TYPE(C);
    /** create an iterator for @b d */
    inline
    explicit FrontToBackIterator (Deque& d)
      : _pointer(d._front), _begin(d._data), _end(d._end), _afterLast(d._back)
    {
    }

    /** true if there exists the next element */
    inline
    bool hasNext() const
    {
      return _pointer != _afterLast;
    }

    /** return the next element */
    inline
    const C& next()
    {
      ASS(hasNext());
      C* res=_pointer;
      _pointer++;
      if(_pointer==_end) {
	_pointer=_begin;
      }
      return *res;
    }

  private:
    C* _pointer;
    C* _begin;
    C* _end;
    C* _afterLast;
  };

  /**
   * Iterator iterates over the elements of a deque from back to front.
   *
   *  @warning The contents of the stack should not be changed by
   *           other operations when a stack is traversed using an
   *           iterator
   */
  class BackToFrontIterator {
  public:
    DECL_ELEMENT_TYPE(C);
    /** create an iterator for @b d */
    inline
    explicit BackToFrontIterator (Deque& d)
      : _pointer(d._back), _begin(d._data), _end(d._end), _last(d._front)
    {
    }

    /** true if there exists the next element */
    inline
    bool hasNext() const
    {
      return _pointer != _last;
    }

    /** return the next element */
    inline
    const C& next()
    {
      ASS(hasNext());
      if(_pointer==_begin) {
	_pointer=_end;
      }
      _pointer--;
      return *_pointer;
    }

  private:
    C* _pointer;
    C* _begin;
    C* _end;
    C* _last;
  };


protected:
  /** Capacity of the stack */
  size_t _capacity;
  /** the stack itself */
  C* _data;
  /** points at the element at the front of the deque */
  C* _front;
  /** points at the element after the back of the deque */
  C* _back;
  /** points after the last allocated element of _data */
  C* _end;

  bool shouldExpand()
  {
    return _back==_front-1 || (_front==_data && _back==_end-1);
  }

  /**
   * Expand the stack. Note: the function heavily uses
   * the fact that the expansion happens exactly when _cursor=_end
   * @since 11/03/2006 Redmond
   */
  void expand ()
  {
    CALL("Deque::expand");

    ASS(shouldExpand());

    size_t curSize=size();
    size_t newCapacity = 2 * _capacity;

    // allocate new stack and copy old stack's content to the new place
    void* mem = ALLOC_KNOWN(newCapacity*sizeof(C),"Deque<>");

    C* newData = static_cast<C*>(mem);
    C* oldPtr=_front;
    for(size_t i = 0; i<curSize; i++) {
      new(newData+i) C(*oldPtr);
      oldPtr->~C();

      oldPtr++;
      if(oldPtr==_end) {
	oldPtr=_data;
      }
    }
    ASS_EQ(oldPtr, _back);
    // deallocate the old stack
    DEALLOC_KNOWN(_data,_capacity*sizeof(C),"Deque<>");

    _data = newData;
    _front = _data;
    _back = _data + curSize;
    _end = _data + newCapacity;
    _capacity = newCapacity;
  }

};

}

#endif // __Deque__
