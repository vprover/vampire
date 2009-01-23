/**
 * @file VirtualIterator.hpp
 * Defines VirtualIterator which allows iterators over various
 * structures to be stored in the same object.
 */

#ifndef __VirtualIterator__
#define __VirtualIterator__

#include "../Forwards.hpp"

#include "../Debug/Assertion.hpp"
#include "../Debug/Tracer.hpp"

#include "Allocator.hpp"
#include "Exception.hpp"
#include "Reflection.hpp"

namespace Lib {

///@addtogroup Iterators
///@{

template<typename T>
  class VirtualIterator;

/**
 * Base class of objects that provide implementation of
 * VirtualIterator objects.
 */
template<typename T>
class IteratorCore {
public:
  DECL_ELEMENT_TYPE(T);
  IteratorCore() : _refCnt(0) {}
  virtual ~IteratorCore() { ASS(_refCnt==0); }
  virtual bool hasNext() = 0;
  virtual T next() = 0;
  virtual bool knowsSize() const { return false; }
  virtual size_t size() const { INVALID_OPERATION("This iterator cannot retrieve its size."); }

  CLASS_NAME("IteratorCore");
  USE_ALLOCATOR_UNK;
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
  T next() { INVALID_OPERATION("next() called on EmptyIterator object"); };
  bool knowsSize() const { return true; }
  size_t size() const { return 0; }
};

/**
 * Template class of virtual iterators, i.e. iterators that
 * can polymorphically use different implementations.
 */
template<typename T>
class VirtualIterator {
public:
  DECL_ELEMENT_TYPE(T);
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
    return *this;
  }

  /**
   * Remove reference to the iterator core.
   * Return true iff the number of references to
   * the iterator core dropped to zero and it was
   * deleted as a result of it.
   *
   * The returned value can be useful for asserting
   * that the iterator core (and all resources it
   * used) was indeed released.
   */
  inline
  bool drop()
  {
    if(_core) {
	_core->_refCnt--;
	if(!_core->_refCnt) {
	  delete _core;
	  _core=0;
	  return true;
	}
    }
    _core=0;
    return false;
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

  bool knowsSize() const { return _core->knowsSize(); }
  size_t size() const { ASS(knowsSize()); return _core->size(); }
private:
  IteratorCore<T>* _core;
};

template<typename T>
VirtualIterator<ELEMENT_TYPE(T)> vi(T* core)
{
  return VirtualIterator<ELEMENT_TYPE(T)>(core);
}

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

template<typename T, class Inner>
VirtualIterator<T> getProxyIterator(Inner it)
{
  return VirtualIterator<T>(new ProxyIterator<T,Inner>(it));
}


/**
 * Return iterator on C, yielding objects type T.
 *
 * The getContentIterator method makes it possible to
 * iterate on arbitrary containers. Usual implementation
 * of this functionality is some Iterable<T> interface,
 * that would be implemented by those containers. This
 * would however lead to the use of virtual methods,
 * which we'd like to avoid, especially in trivial
 * containers, such as List.
 *
 * Overloads of this method, that allow for iteration on
 * different containers are usually defined together
 * with those containers (so we avoid including all their
 * header files here).
 */
template<typename T, class C>
VirtualIterator<T> getContentIterator(C& c)
{
  return getProxyIterator<T>(C::Iterator(c));
}


template<class Arr>
class ArrayishObjectIterator
: public IteratorCore<ELEMENT_TYPE(Arr)>
{
public:
  ArrayishObjectIterator(Arr& arr) : _arr(arr),
  _index(0), _size(_arr.size()) {}
  ArrayishObjectIterator(Arr& arr, size_t size) : _arr(arr),
  _index(0), _size(size) {}
  bool hasNext() { return _index<_size; }
  ELEMENT_TYPE(Arr) next() { ASS(_index<_size); return _arr[_index++]; }
  bool knowsSize() { return true;}
  bool size() { return _size;}
private:
  Arr& _arr;
  size_t _index;
  size_t _size;
};

template<typename T>
class PointerIterator
: public IteratorCore<T>
{
public:
  PointerIterator(T* first, T* afterLast) :
    _curr(first), _afterLast(afterLast) {}
  bool hasNext() { ASS(_curr<=_afterLast); return _curr!=_afterLast; }
  T next() { ASS(hasNext()); return *(_curr++); }
private:
  T* _curr;
  T* _afterLast;
};

///@}

}

#endif
