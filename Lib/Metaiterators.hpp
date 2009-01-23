/**
 * @file Metaiterators.hpp
 * Defines class Metaiterators.
 */


#ifndef __Metaiterators__
#define __Metaiterators__

#include <utility>

#include "../Forwards.hpp"

#include "List.hpp"
#include "Set.hpp"
#include "VirtualIterator.hpp"

namespace Lib {

///@addtogroup Iterators
///@{


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
  bool knowsSize() const { return true; }
  size_t size() const { return 1; }
private:
  bool _finished;
  T _el;
};

template<typename T>
VirtualIterator<T> getSingletonIterator(T el)
{
  return vi( new SingletonIterator<T>(el) );
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
  return vi( new StaticCastIterator<To,Inner>(it) );
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
  bool knowsSize() const { return _it1.knowsSize() && _it2.knowsSize(); }
  size_t size() const { return _it1.size()+_it2.size(); }
private:
  bool _first;
  VirtualIterator<T> _it1;
  VirtualIterator<T> _it2;
};

template<typename T>
VirtualIterator<T> getConcatenatedIterator(VirtualIterator<T> it1, VirtualIterator<T> it2)
{
  return vi( new CatIterator<T>(it1, it2) );
}



/**
 * Implementation object for VirtualIterator, that yields elements
 * of its inner iterator transformed by specified functor.
 */
template<typename Inner, typename Functor>
class MappingIterator
: public IteratorCore<RETURN_TYPE(Functor)>
{
public:
  explicit MappingIterator(Inner inner, Functor func)
  : _inner(inner), _func(func) {}
  bool hasNext() { return _inner.hasNext(); };
  RETURN_TYPE(Functor) next() { return _func(_inner.next()); };
private:
  Inner _inner;
  Functor _func;
};

template<typename Inner, typename Functor>
VirtualIterator<RETURN_TYPE(Functor)> getMappingIterator(Inner it, Functor f)
{
  return vi( new MappingIterator<Inner, Functor>(it, f) );
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
  return vi( new ConstructingIterator<Constructor, Inner>(it) );
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
    CALL("FlatteningIterator::hasNext");
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
  return vi( new FlatteningIterator<T>(it) );
}

template<typename T>
struct VIEncapsulator
{
  DECL_RETURN_TYPE(VirtualIterator<T>);
  OWN_RETURN_TYPE operator() (IteratorCore<T>* obj)
  {
    return VirtualIterator<T>(obj);
  }
};

template<typename T>
VirtualIterator<T> getFlattenedIterator(VirtualIterator<IteratorCore<T>* > it)
{
  VirtualIterator<VirtualIterator<T> > eIt=
    getMappingIterator(it, VIEncapsulator<T>());
  return getFlattenedIterator(eIt);
}


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

/**
 * Return iterator, that yields the same values in
 * the same order as @b it. Benefit of this iterator
 * is, that @b it object is used only during
 * initialization. (So it's underlying object can be
 * freed and the returned iterator will remain valid.)
 */
template<typename T, class Inner>
VirtualIterator<T> getPersistentIterator(Inner it)
{
  return vi( new PersistentIterator<T,Inner>(it) );
}


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

/**
 * Return iterator, that yields unique values yielded by @b it.
 * Those values are yielded in arbitrary order.
 *
 * @b it object is used only during initialization.
 */
template<typename T, class Inner>
VirtualIterator<T> getUniquePersistentIterator(Inner it)
{
  return vi( new UniquePersistentIterator<T,Inner>(it) );
}

/**
 * Return iterator, that yields unique values yielded by @b it.
 * Those values are yielded in arbitrary order.
 *
 * @b it object is used only during initialization.
 */
template<typename T>
VirtualIterator<T> getUniquePersistentIterator(VirtualIterator<T> it)
{
  return vi( new UniquePersistentIterator<T,VirtualIterator<T> >(it) );
}


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

/**
 * Return iterator, that yields objects @b from,
 * (@b from)++, ((@b from)++)++,... until it reaches
 * object @b to. The @b to object is not yielded.
 */
template<typename T>
VirtualIterator<T> getRangeIterator(T from, T to)
{
  return vi( new RangeIterator<T>(from, to) );
}

template<typename T>
class CombinationIterator
: public IteratorCore<pair<T,T> >
{
public:
  CombinationIterator(T from, T to)
  : _first(from), _second(from), _afterLast(to)
  {
    ASS_LE(from,to);
    if(from!=to) {
      moveToNext();
    }
  }
  bool hasNext()
  { ASS_LE(_first,_afterLast); return _second!=_afterLast; }
  pair<T,T> next()
  {
    ASS(hasNext());
    pair<T,T> res=pair<T,T>(_first,_second);
    moveToNext();
    return res;
  }
private:
  void moveToNext()
  {
    _second++;
    ASS_LE(_second,_afterLast);
    if(_second==_afterLast) {
      _first++;
      _second=_first;
      _second++;
      //now, if _second==_afterLast, there's no combination left
    }
  }
  T _first;
  T _second;
  T _afterLast;
};

/**
 * Return iterator, that all unordered pairs from set {@b from,
 * (@b from)++, ((@b from)++)++,..., @b to}\{@b to}. This means
 * that for a singleton set, nothing is returned.
 */
template<typename T>
VirtualIterator<pair<T,T> > getCombinationIterator(T from, T to)
{
  return vi( new CombinationIterator<T>(from, to) );
}


template<typename C, typename D>
class PairRightPushingIterator
: public IteratorCore<pair<C,D> >
{
public:
  PairRightPushingIterator(C c, VirtualIterator<D> dit)
  : _c(c), _dit(dit) {}

  bool hasNext() { return _dit.hasNext(); }
  pair<C,D> next() { return pair<C,D>(_c, _dit.next()); }
private:
  C _c;
  VirtualIterator<D> _dit;
};

/**
 * Given pair of an object A and an iterator I, return
 * an iterator J, that yields pairs (A,C), where C are
 * objects returned by iterator I. This virtually pushes
 * the pair structure into the iterator I.
 */
template<typename C, typename D>
VirtualIterator<pair<C,D> > pushPairIntoRightIterator(pair<C, VirtualIterator<D> > obj)
{
  return vi( new PairRightPushingIterator<C,D>(obj.first, obj.second) );
}

template<typename C, typename D>
VirtualIterator<pair<C,D> > pushPairIntoRightIterator(C c, VirtualIterator<D> dit)
{
  return vi( new PairRightPushingIterator<C,D>(c, dit) );
}

template<typename C, typename D>
class RightPushedPair
{
public:
  RightPushedPair(pair<C,D> p) : _p(p) {}
  pair<C,D> get() { return _p; }
private:
  pair<C,D> _p;
};

/**
 * Given pair of an object A and an iterable object B, return
 * an iterable object, that contains pairs (A,C), where C are
 * objects from B. So this virtually pushes the pair structure
 * into the iterable object B.
 */
template<typename C, typename D>
RightPushedPair<C,D> pushPairIntoRightIterable(pair<C, D> obj)
{
  return RightPushedPair<C,D>(obj);
}

template<typename C, typename D>
struct PushPairIntoRightIterableFn
{
  DECL_RETURN_TYPE(RightPushedPair<C,D>);
  OWN_RETURN_TYPE operator()(pair<C, D> obj)
  {
    return pushPairIntoRightIterable(obj);
  }
};

/** See VirtualIterator.hpp */
template<typename C, typename D>
VirtualIterator<pair<C,ELEMENT_TYPE(D)> > getContentIterator(RightPushedPair<C,D> obj)
{
  return pushPairIntoRightIterator(
	  pair<C,VirtualIterator<ELEMENT_TYPE(D)> >(
		  obj.get().first,
		  getContentIterator(obj.get().second) ) );
}

/**
 * Wraps a context around specified iterator.
 *
 * Context is an object of type @b Ctx with methods
 * void enter(T)
 * void leave(T)
 * where @b T is the return type of inner iterator.
 * Method enter is called before an element of inner
 * iterator is yielded (with this element as a parameter),
 * and leave is called when this element becomes no longer
 * needed (after the hasNext method is called next time,
 * or when the iterator is being destroyed).
 */
template<class Inner, class Ctx>
class ContextualIterator
: public IteratorCore<ELEMENT_TYPE(Inner)>
{
public:
  ContextualIterator(Inner iit, Ctx context)
  : _inContext(false), _iit(iit), _context(context) {}

  ~ContextualIterator()
  {
    assureContextLeft();
  }
  bool hasNext()
  {
    assureContextLeft();
    return _iit.hasNext();
  }
  ELEMENT_TYPE(Inner) next()
  {
    ASS(!_inContext);
    _current=_iit.next();
    _context.enter(_current);
    _inContext=true;
    return _current;
  }
private:
  void assureContextLeft()
  {
    if(_inContext) {
      _context.leave(_current);
      _inContext=false;
    }
  }

  bool _inContext;
  ELEMENT_TYPE(Inner) _current;
  Inner _iit;
  Ctx _context;
};

template<class Inner, class Ctx>
VirtualIterator<ELEMENT_TYPE(Inner)> getContextualIterator(Inner it, Ctx context)
{
  return vi( new ContextualIterator<Inner,Ctx>(it, context) );
}


///@}

}

#endif /* __Metaiterators__ */
