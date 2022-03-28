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
 * @file Stack.hpp
 * Defines a class of flexible-sized stacks
 *
 * @since 04/06/2005 Manchester
 */

#ifndef __Stack__
#define __Stack__

#include <cstdlib>

#include "Forwards.hpp"

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "Backtrackable.hpp"

namespace std
{
template<typename T>
void swap(Lib::Stack<T>& s1, Lib::Stack<T>& s2);
}

namespace Lib {

template<typename C>
struct Relocator<Stack<C> >;

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
  template<typename U>
  friend void std::swap(Stack<U>&,Stack<U>&);

  class Iterator;
  class ConstIterator;
  class BottomFirstIterator;

  DECL_ELEMENT_TYPE(C);
  DECL_ITERATOR_TYPE(Iterator);

  CLASS_NAME(Stack);
  USE_ALLOCATOR(Stack);
  DECLARE_PLACEMENT_NEW;


  /**
   * Create a stack having initialCapacity.
   */
  inline
  explicit Stack (size_t initialCapacity=0)
    : _capacity(initialCapacity)
  {
    CALL("Stack::Stack");

    if(_capacity) {
      void* mem = ALLOC_KNOWN(_capacity*sizeof(C),className());
      _stack = static_cast<C*>(mem);
    }
    else {
      _stack = 0;
    }
    _cursor = _stack;
    _end = _stack+_capacity;
  }

  inline
  void reserve(size_t capacity) 
  {
    CALL("Stack::reserve(size_t)");
    if (_capacity >= capacity) {
      return;
    }
    C* mem = static_cast<C*>(ALLOC_KNOWN(capacity*sizeof(C),className()));
    if (_stack) {
      for (unsigned i = 0; i < size(); i++) {
        ::new(&mem[i]) C(std::move((*this)[i]));
      }
      DEALLOC_KNOWN(_stack,_capacity*sizeof(C),className());

      _cursor = mem + (_cursor - _stack);
      _capacity = capacity;
      _stack = mem;
      _end = _stack + _capacity;
    } else {
      _stack = mem;
      _cursor = mem;
      _capacity = capacity;
      _end = _stack + _capacity;
    }
  }


  Stack(const Stack& s)
   : _capacity(s._capacity)
  {
    CALL("Stack::Stack(const Stack&)");

    if(_capacity) {
      void* mem = ALLOC_KNOWN(_capacity*sizeof(C),className());
      _stack = static_cast<C*>(mem);
    }
    else {
      _stack = 0;
    }
    _cursor = _stack;
    _end = _stack+_capacity;

    loadFromIterator(BottomFirstIterator(const_cast<Stack&>(s)));
  }

  Stack(Stack&& s) noexcept
  {
    CALL("Stack::Stack(Stack&& s)");

    _capacity = 0;
    _stack = _cursor = _end = nullptr;

    std::swap(*this,s);
  }

  /** De-allocate the stack
   * @since 13/01/2008 Manchester
   */
  inline ~Stack()
  {
    CALL("Stack::~Stack");

    //The while cycle is completely eliminated by compiler
    //in "-O6 -DVDEBUG=0" mode for types without destructor,
    //so this destructor is constant time.
    C* p=_cursor;
    while(p!=_stack) {
      (--p)->~C();
    }
    if(_stack) {
      DEALLOC_KNOWN(_stack,_capacity*sizeof(C),className());
    }
    else {
      ASS_EQ(_capacity,0);
    }
  }

  Stack& operator=(const Stack& s)
  {
    CALL("Stack::operator=");

    if(&s == this) {
      return *this;
    }
    reset();
    loadFromIterator(BottomFirstIterator(const_cast<Stack&>(s)));
    return *this;
  }

  Stack& operator=(Stack&& s) noexcept
  {
    CALL("Stack::operator=&&");

    std::swap(*this,s);
    return *this;
  }


  /**
   * Put all elements of an iterator onto the stack.
   */
  template<class It>
  void loadFromIterator(It it) {
    CALL("Stack::loadFromIterator");

    // TODO check iterator.size() or iterator.sizeHint()
    while(it.hasNext()) {
      push(it.next());
    }
  }

  /**
   * Put all elements of an iterator onto the stack.
   */
  template<class It>
  void moveFromIterator(It it) {
    CALL("Stack::loadFromIterator");

    // TODO check iterator.size() or iterator.sizeHint()
    while(it.hasNext()) {
      push(std::move(it.next()));
    }
  }


  /**
   * Create a new stack with the contents of the itererator.
   */
  template<class It>
  static Stack fromIterator(It it) {
    CALL("Stack::fromIterator");
    Stack out;
    out.loadFromIterator(it);
    return out;
  }

  Iterator iter() &
  { return Iterator(*this); }

  ConstIterator iter() const&
  { return ConstIterator(*this); }

  /* a first-in-first-out iterator  */
  BottomFirstIterator iterFifo() const 
  { return BottomFirstIterator(*this); }

  /* a first-in-first-out iterator  */
  BottomFirstIterator iterFifoMut() const 
  { return BottomFirstIterator(*this); }

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

  /** Return a const reference to the n-th element of the stack */
  inline
  const C& operator[](size_t n) const
  {
    ASS(n >= 0);
    ASS(_stack+n < _cursor);

    return _stack[n];
  }

  bool operator==(const Stack& o) const
  {
    CALL("Stack::operator==");

    if(size()!=o.size()) {
      return false;
    }
    size_t sz = size();
    for(size_t i=0; i!=sz; ++i) {
      if((*this)[i]!=o[i]) {
	return false;
      }
    }
    return true;
  }

  bool operator!=(const Stack& o) const
  { return !((*this)==o); }

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
   * Return the top but one of the stack.
   */
  inline
  C& scnd() const
  {
    ASS(_cursor > _stack + 1);
    ASS(_cursor <= _end);

    return _cursor[-2];
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
  void push(const C& elem)
  {
    CALL("Stack::push");

    if (_cursor == _end) {
      expand();
    }
    ASS(_cursor < _end);
    ::new(_cursor) C(elem);
    _cursor++;
  } // Stack::push()

  /**
   * Push new element on the stack (move semantics version).
   * @since 11/08/2020 
   */
  inline
  void push(C&& elem)
  {
    CALL("Stack::push");

    if (_cursor == _end) {
      expand();
    }
    ASS(_cursor < _end);
    ::new(_cursor) C(std::move(elem));
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

    C res = std::move(*_cursor);
    _cursor->~C();

    return res;
  } // Stack::pop()


  inline
  void pop(unsigned cnt)
  {
    CALL("Stack::pop(unsigned)");
    while (cnt-- != 0) 
      pop();
  } // Stack::pop(unsigned)

  /**
   * If the element @b el is present in the stack, remove it and return
   * true, otherwise return false.
   */
  bool remove(C el)
  {
    Iterator it(*this);
    while(it.hasNext()) {
      if(it.next()==el) {
        it.del();
        return true;
      }
    }
    return false;
  }

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

  inline
  C* begin() const
  {
    return _stack;
  }

  /** Empties the stack. */
  inline
  void reset()
  {
    C* p=_cursor;
    while(p!=_stack) {
      (--p)->~C();
    }
    _cursor = _stack;
  }

  /** Sets the length of the stack to @b len
   *  @since 27/12/2007 Manchester */
  inline
  void truncate(size_t len)
  {
    ASS_LE(len,length());
    C* p=_stack+len;
    while(p!=_cursor) {
      (p++)->~C();
    }
    _cursor = _stack+len;
  } // truncate

  /** Return the number of elements in the stack, same as size() */
  inline
  size_t length() const
  { return _cursor - _stack; }

  /** Return the number of elements in the stack, same as length() */
  inline
  size_t size() const
  { return _cursor - _stack; }

  bool find(const C& el) const
  {
    CALL("Stack::find");

    Iterator it(const_cast<Stack&>(*this));
    while(it.hasNext()) {
      if(it.next()==el) {
	return true;
      }
    }
    return false;
  }

#if VDEBUG
  vstring toString()
  {
    vstring ret = "[";
    Iterator it(const_cast<Stack&>(*this));
    while(it.hasNext()){
      C el = it.next();
      ret += Int::toString(static_cast<unsigned int>(el));
      if(it.hasNext()){ ret +=",";}
    }
    return ret+"]";
  }

#endif

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
    DECL_ELEMENT_TYPE(C);
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
#if VDEBUG
      _last = 2;
#endif

      return _pointer != _stack._stack;
    }

    /** return the next element */
    inline
    C& next()
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

    /** Replace the last element returned by next() */
    inline
    void replace(C val)
    {
      ASS(_pointer < _stack._cursor);
      ASS(_pointer >= _stack._stack);
      ASS(_last == 1);

      *_pointer = val;
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

  class ConstIterator {
  public:
    DECL_ELEMENT_TYPE(C);
    /** create an iterator for @b s */
    inline
    explicit ConstIterator (const Stack& s)
      : _pointer(s._cursor),
	_stack(s)
    {
    }

    /** true if there exists the next element */
    inline
    bool hasNext() const
    {
      return _pointer != _stack._stack;
    }

    /** return the next element */
    inline
    C next()
    {
      ASS(_pointer > _stack._stack);
      _pointer--;
      return *_pointer;
    }

  private:
    /** pointer to the stack element returned by next() */
    C* _pointer;
    /** stack over which we iterate */
    const Stack& _stack;
  };

  typedef Iterator DelIterator;
  typedef ConstIterator TopFirstIterator;

  /**
   * An iterator object that for stack @b s first yields element s[0]
   * and the element s.top() is last.
   */
  class BottomFirstIterator {
  public:
    DECL_ELEMENT_TYPE(C);
    /** create an iterator for @b s */
    inline
    explicit BottomFirstIterator (const Stack& s)
      : _pointer(s._stack),
	_afterLast(s._cursor)
    {
    }

    /** true if there exists the next element */
    inline
    bool hasNext() const
    {
      CALL("Stack::BottomFirstIterator::hasNext()")
      ASS_LE(_pointer, _afterLast);
      return _pointer != _afterLast;
    }

    /** return the next element */
    inline
    const C& next()
    {
      CALL("Stack::BottomFirstIterator::next()")
      ASS_L(_pointer, _afterLast);
      return *(_pointer++);
    }

  private:
    /** pointer to the stack element returned by next call to @b next() */
    C* _pointer;
    /** pointer to element after the last element on the stack */
    C*  _afterLast;
  };

  /**
   * Iterator iterates over the elements of a stack from s[0] to s.top()
   * and can delete elements from the stack without changing the order of
   * the remaining elements.
   *  @warning The contents of the stack should not be changed by
   *           other operations when a stack is traversed using an
   *           iterator
   */
  class StableDelIterator {
    StableDelIterator(const StableDelIterator&);
    StableDelIterator& operator=(const StableDelIterator&);
  public:
    DECL_ELEMENT_TYPE(C);
    /** create an iterator for @b s */
    inline
    explicit StableDelIterator (Stack& s)
      : _reader(s._stack),
        _writer(s._stack),
	_stack(s)
#if VDEBUG
      , _last(0)
#endif
    {
    }

    ~StableDelIterator() {
      if(_reader!=_writer) {
	//if we deleted something, we must go through the rest of the stack
	//to shift the remaining elements
	while(hasNext()) {
	  next();
	}
      }
    }

    /** true if there exists the next element */
    inline
    bool hasNext()
    {
#if VDEBUG
      _last = 2;
#endif

      if(_reader==_stack._cursor) {
	if(_reader!=_writer) {
	  _stack._cursor = _writer;
	  _reader = _writer; //this is to handle properly repeated calls to this function
	}
	return false;
      }
      ASS_L(_reader,_stack._cursor);
      return true;
    }

    /** return the next element */
    inline
    C next()
    {
      ASS(_reader < _stack._cursor);
      ASS(_last == 2);
#if VDEBUG
      _last = 1;
#endif
      if(_reader!=_writer) {
	ASS_L(_writer, _reader);
	*_writer = *_reader;
      }
      const C& res = *_reader;
      _reader++;
      _writer++;

      return res;
    }

    /** Delete the last element returned by next() */
    inline
    void del()
    {
      ASS(_writer <= _stack._cursor);
      ASS(_writer >= _stack._stack);
      ASS(_last == 1);
#if VDEBUG
      _last = 3;
#endif

      _writer--;
    }

    /** Replace the last element returned by next() */
    inline
    void replace(C val)
    {
      ASS(_writer < _stack._cursor);
      ASS(_writer >= _stack._stack);
      ASS(_last == 1);

      *_writer = val;
    }
  private:
    /** pointer to the stack element returned by next() */
    C* _reader;
    /** pointer to the stack element returned by next() */
    C* _writer;
    /** stack over which we iterate */
    Stack& _stack;
#if VDEBUG
    /** last operation: 0(none), 1(next), 2(hasNext), 3(del) */
    mutable int _last;
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

    size_t newCapacity = _capacity ? (2 * _capacity) : 8;

    // allocate new stack and copy old stack's content to the new place
    void* mem = ALLOC_KNOWN(newCapacity*sizeof(C),className());

    C* newStack = static_cast<C*>(mem);
    if(_capacity) {
      for (size_t i = 0; i<_capacity; i++) {
        ::new(newStack+i) C(std::move(_stack[i]));
        _stack[i].~C();
      }
      // deallocate the old stack
      DEALLOC_KNOWN(_stack,_capacity*sizeof(C),className());
    }

    _stack = newStack;
    _cursor = _stack + _capacity;
    _end = _stack + newCapacity;
    _capacity = newCapacity;
  } // Stack::expand

  class PushBacktrackObject: public BacktrackObject
  {
    Stack* st;
  public:
    CLASS_NAME(Stack::PushBacktrackObject);
    USE_ALLOCATOR(Stack::PushBacktrackObject);
    
    PushBacktrackObject(Stack* st) : st(st) {}
    void backtrack() { st->pop(); }
  };
public:

  void backtrackablePush(C v, BacktrackData& bd)
  {
    push(v);
    bd.addBacktrackObject(new PushBacktrackObject(this));
  }

  friend ostream& operator<<(ostream& out, const Stack<C>& s) {
    out << "[";
    auto iter = s.begin();
    if(iter != s.end()) {
      out << " " << *iter++;
      while (iter != s.end()) {
        out << ", " << *iter++;
      }
    }
    out << " ]";
    return out;
  }

  Stack(std::initializer_list<C> cont)
   : Stack(cont.size())
  {
    CALL("Stack::Stack(initializer_list<C>)");

    for (auto const& x : cont) {
      push(x);
    }
  }

};

template<typename C>
struct Relocator<Stack<C> >
{
  static void relocate(Stack<C>* oldStack, void* newAddr)
  {
    ::new(newAddr) Stack<C>(std::move(*oldStack));
    oldStack->~Stack<C>();
  }
};


} // namespace Lib

namespace std
{

template<typename T>
void swap(Lib::Stack<T>& s1, Lib::Stack<T>& s2)
{
  CALL("std::swap(Stack&,Stack&)");

  swap(s1._capacity, s2._capacity);
  swap(s1._cursor, s2._cursor);
  swap(s1._end, s2._end);
  swap(s1._stack, s2._stack);
}

}

#endif
