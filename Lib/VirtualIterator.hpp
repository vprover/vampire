/**
 * @file VirtualIterator.hpp
 * Defines VirtualIterator which allows iterators over various
 * structures to be stored in the same object. 
 */

#ifndef __VirtualIterator__
#define __VirtualIterator__


namespace Lib {

template<typename T>
  class VirtualIterator;

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

template<typename T>
class VirtualIterator {
public:
  VirtualIterator() : _core(0) {}
  explicit VirtualIterator(IteratorCore<T>* core) : _core(core) { _core->_refCnt++;}
  VirtualIterator(const VirtualIterator& obj) : _core(obj._core) { _core->_refCnt++;}
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
  bool hasNext() { return _core->hasNext(); }
  T next() { return _core->next(); }
private:
  IteratorCore<T>* _core;
};


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



}

#endif
