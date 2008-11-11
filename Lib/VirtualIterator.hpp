/**
 * @file VirtualIterator.hpp
 * Defines VirtualIterator which allows iterators over various
 * structures to be stored in the same object. 
 */

#ifndef __VirtualIterator__
#define __VirtualIterator__

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

namespace Lib {

template<typename T>
  class VirtualIterator;

/**
 * Base class of objects that provide implementation of 
 * VirtualIterator objects.
 */
template<typename T>
class IteratorCore {
public:
  IteratorCore() : _refCnt(0) {}
  virtual ~IteratorCore() { ASS(_refCnt==0); }
  virtual bool hasNext() = 0;
  virtual T next() = 0;
private:
  mutable int _refCnt;
  
  friend class VirtualIterator<T>;
};

/**
 * Implementation object for VirtualIterator, that represents
 * an empty iterator.
 */
template<typename T>
class EmptyIterator 
: public IteratorCore<T>
{
public:
  EmptyIterator() {}
  bool hasNext() { return false; };
  T next() { ASSERTION_VIOLATION; };
};

/**
 * Template class of virtual iterators, i.e. iterators that
 * can polymorphically use different implementations.
 */
template<typename T>
class VirtualIterator {
public:
  static VirtualIterator getEmpty()
  {
    static VirtualIterator inst(new EmptyIterator<T>());
    return inst;
  }
  inline
  VirtualIterator() : _core(0) {}
  inline
  explicit VirtualIterator(IteratorCore<T>* core) : _core(core) { _core->_refCnt++;}
  inline
  VirtualIterator(const VirtualIterator& obj) : _core(obj._core) { _core->_refCnt++;}
  inline
  ~VirtualIterator() 
  { 
    if(_core) {
	_core->_refCnt--; 
	if(!_core->_refCnt) {
	  delete _core;
	}
    }
  }
  VirtualIterator& operator=(const VirtualIterator& obj) 
  {
    CALL("VirtualIterator::operator=");
    
    IteratorCore<T>* oldCore=_core;
    _core=obj._core;
    if(_core) {
	_core->_refCnt++;
    }
    if(oldCore) {
	oldCore->_refCnt--;
	if(!oldCore->_refCnt) {
	  delete oldCore;
	}
    }
  }

  /** True if there exists next element */
  inline
  bool hasNext() { return _core->hasNext(); }
  /**
   * Return the next value
   * @warning hasNext() must have been called before
   */
  inline
  T next() { return _core->next(); }
private:
  IteratorCore<T>* _core;
};


/**
 * Implementation object for VirtualIterator, that represents
 * an iterator that yields only one object.
 */
template<typename T>
class SingletonIterator 
: public IteratorCore<T>
{
public:
  explicit SingletonIterator(T el) : _finished(false), _el(el) {}
  bool hasNext() { return _finished; };
  T next() { ASS(!_finished); _finished=true; return _el; };
private:
  bool _finished;
  T _el;
};

/**
 * Implementation object for VirtualIterator, that can proxy any
 * non-virtual iterator, that supports hasNext() and next() methods.
 */
template<typename T, class Inner>
class ProxyIterator 
: public IteratorCore<T>
{
public:
  explicit ProxyIterator(Inner inn) :_inn(inn) {}
  bool hasNext() { return _inn.hasNext(); };
  T next() { return _inn.next(); };
private:
  Inner _inn;
};


/**
 * Implementation object for VirtualIterator, that can proxy any
 * non-virtual iterator, that supports hasNext() and next() methods, 
 * and yields only those elements, for which Predicate::eval() 
 * returns true.
 */
template<typename T, class Inner, class Predicate>
class FilteredIterator 
: public IteratorCore<T>
{
public:
  explicit FilteredIterator(Inner inn) :_inn(inn), _nextStored(false) {}
  bool hasNext()
  {
    if(_nextStored) {
      return true;
    }
    while(_inn.hasNext()) {
      _next=_inn.next();
      if(Predicate::eval(_next)) {
	_nextStored=true;
	return true;
      }
    }
    return false; 
  };
  T next() 
  {
    if(!_nextStored) {
      bool res=hasNext();
      ASS(res);
      ASS(_nextStored)
    }
    _nextStored=false;
    return _next;
  };
private:
  Inner _inn;
  T _next;
  bool _nextStored;
};

/**
 * Implementation object for VirtualIterator, that can proxy any
 * non-virtual iterator, that supports hasNext() and next() methods, 
 * and yields its elements only until Predicate::eval() returns false
 * for a value.
 */
template<typename T, class Inner, class Predicate>
class WhileLimitedIterator 
: public IteratorCore<T>
{
public:
  explicit WhileLimitedIterator(Inner inn) :_inn(inn), _nextStored(false) {}
  bool hasNext()
  {
    if(!_nextStored) {
      if(!_inn.hasNext()) {
        return false;
      }
      _next=_inn.next();
      _nextStored=true;
    }
    return Predicate::eval(_next);
  };
  T next() 
  {
    if(!_nextStored) {
      bool res=hasNext();
      ASS(res);
      ASS(_nextStored)
    }
    _nextStored=false;
    return _next;
  };
private:
  Inner _inn;
  T _next;
  bool _nextStored;
};


/**
 * Implementation object for VirtualIterator, that concatenates
 * two other virtual iterators.
 */
template<typename T>
class CatIterator 
: public IteratorCore<T>
{
public:
  CatIterator(VirtualIterator<T> it1, VirtualIterator<T> it2) 
  	:_first(true), _it1(it1), _it2(it2) {}
  bool hasNext() 
  {
    if(_first) {
      if(_it1.hasNext()) {
	return true;
      }
      _first=false;
    }
    return  _it2.hasNext();
  };
  /**
   * Return the next value
   * @warning hasNext() must have been called before
   */
  T next()
  {
    if(_first) {
      //_it1 contains the next value, as hasNext must have 
      //been called before. (It would have updated the 
      //_first value otherwise.)
      return _it1.next();
    }
    return  _it2.next();
  };
private:
  bool _first;
  VirtualIterator<T> _it1;
  VirtualIterator<T> _it2;
};


}

#endif
