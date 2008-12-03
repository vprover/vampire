/**
 * @file Stack.hpp
 * Defines a class of flexible-sized stacks
 *
 * @since 04/06/2005 Manchester
 */

#ifndef __Stack__
#define __Stack__

#include <cstdlib>

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "BacktrackData.hpp"

namespace Lib {

/**
 * Class of flexible-size generic stacks.
 * @since 11/03/2006 Bellevue
 * @since 14/03/2006 Bellevue reimplemented in a slightly more efficient way.
 * @since 19/05/2007 Manchester reimplemented back due to errors
 */
template<class C>
class Stack
{
public:
  /**
   * Create a stack having initialCapacity.
   */
  inline
  Stack (size_t initialCapacity)
    : _capacity(initialCapacity)
  {
    CALL("Stack::Stack");
    ASS(initialCapacity > 0);

    void* mem = ALLOC_KNOWN(initialCapacity*sizeof(C),"Stack<>");
    _stack = new(mem) C[_capacity];
    _cursor = _stack;
    _end = _stack+_capacity;
  }

  /** De-allocate the stack
   * @since 13/01/2008 Manchester
   */
  inline ~Stack()
  {
    CALL("Stack::~Stack");
    DEALLOC_KNOWN(_stack,_capacity*sizeof(C),"Stack<>");
  }

  /**
   * Return a reference to the n-th element of the stack.
   */
  inline
  C& operator[](size_t n)
  {
    ASS(n >= 0);
    ASS(_stack+n < _cursor);

    return _stack[n];
  } // operator[]

  /** Return a reference to the n-th element of the stack */
  inline
  const C& operator[](size_t n) const
  {
    ASS(n >= 0);
    ASS(_stack+n < _cursor);

    return _stack[n];
  }

  /**
   * Return the top of the stack.
   * @since 11/03/2006 Bellevue
   */
  inline
  C& top() const
  {
    ASS(_cursor > _stack);
    ASS(_cursor <= _end);

    return _cursor[-1];
  } // Stack::top()

  /**
   * Set top to a new value.
   * @since 14/03/2006 Bellevue
   */
  inline
  void setTop(C elem)
  {
    CALL("Stack::setTop");
    ASS(_cursor > _stack);
    ASS(_cursor <= _end);

    _cursor[-1] = elem;
  } // Stack::top()

  /**
   * True if the stack is empty.
   * @since 11/03/2006 Bellevue
   */
  inline
  bool isEmpty() const
  {
    return _cursor == _stack;
  } // Stack::isEmpty()

  /**
   * True if the stack is non-empty.
   * @since 11/03/2006 Bellevue
   */
  inline
  bool isNonEmpty() const
  {
    return _cursor != _stack;
  } // Stack::nonempty()

  /**
   * Push new element on the stack.
   * @since 11/03/2006 Bellevue
   */
  inline
  void push(C elem)
  {
    CALL("Stack::push");

    if (_cursor == _end) {
      expand();
    }
    ASS(_cursor < _end);
    *_cursor = elem;
    _cursor++;
  } // Stack::push()

  /**
   * Pop the stack and return the popped element.
   * @since 11/03/2006 Bellevue
   */
  inline
  C pop()
  {
    CALL("Stack::pop");

    ASS(_cursor > _stack);
    _cursor--;

    return *_cursor;
  } // Stack::pop()

//   /**
//    * Return the beginning of the stack, can be used together with end()
//    * for iterating over the elements of the stack.
//    * @since 11/03/2006 Bellevue
//    */
//   inline
//   C* begin() const
//   {
//     return _stack;
//   }

  /**
   * Return the element past the end of the stack, can be used together
   * with begin() for iterating over the elements of the stack.
   * @since 11/03/2006 Bellevue
   */
  inline
  C* end() const
  {
    return _cursor;
  }

  /** Empties the stack. */
  inline
  void reset()
  { _cursor = _stack; }

  /** Sets the length of the stack to @b len
   *  @since 27/12/2007 Manchester */
  inline
  void truncate(size_t len)
  {
    ASS(len <= length());

    _cursor = _stack+len;
  } // truncate

  /** Return the number of elements in the stack */
  inline
  size_t length() const
  { return _cursor - _stack; }

  friend class Iterator;

  /** Iterator iterates over the elements of a stack and can
   *  delete elements from the stack.
   *  @warning After deletion the order of elements in the stack
   *           may change
   *  @warning The contents of the stack should not be changed by
   *           other operations when a stack is traversed using an
   *           iterator
   *  @since 13/02/2008 Manchester
   */
  class Iterator {
  public:
    /** create an iterator for @b s */
    inline
    explicit Iterator (Stack& s)
      : _pointer(s._cursor),
	_stack(s)
#if VDEBUG
      , _last(0)
#endif
    {
    }

    /** true if there exists the next element */
    inline
#if VDEBUG
    bool hasNext()
#else
    bool hasNext() const
#endif
    {
      ASS(_last != 2);
#if VDEBUG
      _last = 2;
#endif

      return _pointer != _stack._stack;
    }

    /** return the next element */
    inline
    C next()
    {
      ASS(_pointer > _stack._stack);
      ASS(_last == 2);
#if VDEBUG
      _last = 1;
#endif

      _pointer--;
      return *_pointer;
    }

    /** Delete the last element returned by next() */
    inline
    void del()
    {
      ASS(_pointer < _stack._cursor);
      ASS(_pointer >= _stack._stack);
      ASS(_last == 1);
#if VDEBUG
      _last = 3;
#endif

      *_pointer = _stack.pop();
    }
  private:
    /** pointer to the stack element returned by next() */
    C* _pointer;
    /** stack over which we iterate */
    Stack& _stack;
#if VDEBUG
    /** last operation: 0(none), 1(next), 2(hasNext), 3(del) */
    int _last;
#endif
  };

protected:
  /** Capacity of the stack */
  size_t _capacity;
  /** the stack itself */
  C* _stack;
  /** the cursor, points at the element after the top of the stack */
  C* _cursor;
  /** points to after the last possible value for _cursor */
  C* _end;

  /**
   * Expand the stack. Note: the function heavily uses
   * the fact that the expansion happens exactly when _cursor=_end
   * @since 11/03/2006 Redmond
   */
  void expand ()
  {
    CALL("Stack::expand");

    ASS(_cursor == _end);

    size_t newCapacity = 2 * _capacity;

    // allocate new stack and copy old stack's content to the new place
    void* mem = ALLOC_KNOWN(newCapacity*sizeof(C),"Stack<>");
    C* newStack = new(mem) C[newCapacity];
    for (int i = _capacity-1;i >= 0;i--) {
      newStack[i] = _stack[i];
    }
    // deallocate the old stack
    DEALLOC_KNOWN(_stack,_capacity*sizeof(C),"Stack<>");

    _stack = newStack;
    _cursor = _stack + _capacity;
    _end = _stack + newCapacity;
    _capacity = newCapacity;
  } // Stack::expand

  class PushBacktrackObject: public BacktrackObject
  {
    Stack* st;
  public:
    PushBacktrackObject(Stack* st) : st(st) {}
    void backtrack() { st->pop(); }
  };
public:

  void backtrackablePush(C v, BacktrackData& bd)
  {
    push(v);
    bd.addBacktrackObject(new PushBacktrackObject(this));
  }

};

} // namespace Lib

#endif
