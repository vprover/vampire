/**
 * @file Metaiterators.hpp
 * Defines class Metaiterators.
 */


#ifndef __Metaiterators__
#define __Metaiterators__

#include "List.hpp"
#include "Set.hpp"
#include "VirtualIterator.hpp"

namespace Lib {

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
  bool hasNext() { return !_finished; };
  T next() { ASS(!_finished); _finished=true; return _el; };
private:
  bool _finished;
  T _el;
};

template<typename T>
VirtualIterator<T> getSingletonIterator(T el)
{
  return VirtualIterator<T>(new SingletonIterator<T>(el));
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
 * Implementation object for VirtualIterator, that can casts objects
 * of its inner iterator to target type with static_cast.
 */
template<typename To, class Inner>
class StaticCastIterator
: public IteratorCore<To>
{
public:
  explicit StaticCastIterator(Inner inn) :_inn(inn) {}
  bool hasNext() { return _inn.hasNext(); };
  To next() { return static_cast<To>(_inn.next()); };
private:
  Inner _inn;
};

template<typename To, class Inner>
VirtualIterator<To> getStaticCastIterator(Inner it)
{
  return VirtualIterator<To>(new StaticCastIterator<To,Inner>(it));
}


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
      ALWAYS(hasNext());
      ASS(_nextStored);
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
      ALWAYS(hasNext());
      ASS(_nextStored);
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
 *
 * After the first iterator is empty, pointer to its core is dropped,
 * so that its resources can be released.
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
      _it1.drop();
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

template<typename T>
VirtualIterator<T> getConcatenatedIterator(VirtualIterator<T> it1, VirtualIterator<T> it2)
{
  return VirtualIterator<T>(new CatIterator<T>(it1, it2));
}



/**
 * Implementation object for VirtualIterator, that yields elements
 * of its inner iterator transformed by specified functor.
 */
template<typename DestType, typename Inner, typename Functor>
class MappingIterator
: public IteratorCore<DestType>
{
public:
  explicit MappingIterator(Inner inner, Functor func)
  : _inner(inner), _func(func) {}
  bool hasNext() { return _inner.hasNext(); };
  DestType next() { return _func(_inner.next()); };
private:
  Inner _inner;
  Functor _func;
};

template<typename DestType, typename Inner, typename Functor>
VirtualIterator<DestType> getMappingIterator(Inner it, Functor f)
{
  return VirtualIterator<DestType>(new MappingIterator<DestType, Inner, Functor>(it, f));
}


/**
 * Implementation object for VirtualIterator, that yields elements
 * created by Constructor with parameter from its inner iterator.
 */
template<typename Constructor, typename Inner>
class ConstructingIterator
: public IteratorCore<Constructor*>
{
public:
  explicit ConstructingIterator(Inner inner)
  : _inner(inner) {}
  bool hasNext() { return _inner.hasNext(); };
  Constructor* next() { return new Constructor(_inner.next()); };
private:
  Inner _inner;
};

template<typename Constructor, typename Inner>
VirtualIterator<Constructor*> getConstructingIterator(Inner it)
{
  return VirtualIterator<Constructor*>(new ConstructingIterator<Constructor, Inner>(it));
}


/**
 * Implementation object for VirtualIterator, that flattens
 * VirtualIterator<VirtualIterator<T>> into VirtualIterator<T>.
 *
 * When the inner iterator is empty, pointer to its core is
 * dropped even before the hasNext() method of the outer iterator
 * is called. This could be important in the case, that inner
 * iterators use some resource of the outer iterator, that has to
 * be released by its destructor before calling the outer iterator.
 */
template<typename T>
class FlatteningIterator
: public IteratorCore<T>
{
public:
  typedef VirtualIterator<T> InnerIterator;
  typedef VirtualIterator<InnerIterator> MasterIterator;

  explicit FlatteningIterator(MasterIterator master)
  : _master(master), _current(InnerIterator::getEmpty()) {}
  bool hasNext()
  {
    for(;;) {
      if(_current.hasNext()) {
	return true;
      }
      _current.drop();
      if(!_master.hasNext()) {
	return false;
      }
      _current=_master.next();
    }
  }
  T next()
  {
    ASS(_current.hasNext());
    return _current.next();
  }
private:
  MasterIterator _master;
  InnerIterator _current;
};

template<typename T>
VirtualIterator<T> getFlattenedIterator(VirtualIterator<VirtualIterator<T> > it)
{
  return VirtualIterator<T>(new FlatteningIterator<T>(it));
}

template<typename T>
class VIEncapsulator
{
  VirtualIterator<T> operator() (IteratorCore<T>* obj)
  {
    return VirtualIterator<T>(obj);
  }
};

template<typename T>
VirtualIterator<T> getFlattenedIterator(VirtualIterator<IteratorCore<T>* > it)
{
  VirtualIterator<VirtualIterator<T> > eIt=
    getMappingIterator<VirtualIterator<T> >(it, VIEncapsulator<T>());
  return getFlattenedIterator(eIt);
}


/**
 * Implementation object for VirtualIterator, that can proxy any
 * non-virtual iterator, that supports hasNext() and next() methods.
 */
template<typename T, class Inner>
class PersistentIterator
: public IteratorCore<T>
{
public:
  explicit PersistentIterator(Inner inn)
  : _items(0)
  {
    List<T>** ptr=&_items;
    while(inn.hasNext()) {
      *ptr=new List<T>(inn.next());
      ptr=&(*ptr)->tailReference();
    }
  }
  ~PersistentIterator()
  {
    if(_items) {
      _items->destroy();
    }
  }
  bool hasNext() { return _items; };
  T next()
  {
    return List<T>::pop(_items);
  };
private:

  List<T>* _items;
};

template<typename T, class Inner>
VirtualIterator<T> getPersistentIterator(Inner it)
{
  return VirtualIterator<T>(new PersistentIterator<T,Inner>(it));
}


/**
 * Implementation object for VirtualIterator, that can proxy any
 * non-virtual iterator, that supports hasNext() and next() methods.
 */
template<typename T, class Inner>
class UniquePersistentIterator
: public IteratorCore<T>
{
public:
  explicit UniquePersistentIterator(Inner inn)
  {
    while(inn.hasNext()) {
      _items.insert(inn.next());
    }
    _iit=typename Set<T>::Iterator(_items);
  }
  bool hasNext() { return _iit.hasNext(); };
  T next()
  {
    return _iit.next();
  };
  bool knowsSize() const { return true; }
  size_t size() const { return _items.numberOfElements(); }
private:
  Set<T> _items;
  typename Set<T>::Iterator _iit;
};

template<typename T, class Inner>
VirtualIterator<T> getUniquePersistentIterator(Inner it)
{
  return VirtualIterator<T>(new UniquePersistentIterator<T,Inner>(it));
}

template<typename T>
VirtualIterator<T> getUniquePersistentIterator(VirtualIterator<T> it)
{
  return VirtualIterator<T>(new UniquePersistentIterator<T,VirtualIterator<T> >(it));
}


/**
 * Implementation object for VirtualIterator, that can proxy any
 * non-virtual iterator, that supports hasNext() and next() methods.
 */
template<typename T>
class RangeIterator
: public IteratorCore<T>
{
public:
  RangeIterator(T from, T to)
  : _next(from), _from(from), _to(to) {}
  bool hasNext() { return _next<_to; };
  T next() { return _next++; };
  bool knowsSize() const { return true; }
  size_t size() const { return (_to>_from) ? (_to-_from) : 0; }
private:
  T _next;
  T _from;
  T _to;
};

template<typename T>
VirtualIterator<T> getRangeIterator(T from, T to)
{
  return VirtualIterator<T>(new RangeIterator<T>(from, to));
}

};

#endif /* __Metaiterators__ */
