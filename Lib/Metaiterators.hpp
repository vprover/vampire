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
template<class C>
ITERATOR_TYPE(C) getContentIterator(C& c)
{
  return ITERATOR_TYPE(C)(c);
}


template<class Arr>
class ArrayishObjectIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Arr));
  ArrayishObjectIterator(Arr& arr) : _arr(arr),
  _index(0), _size(_arr.size()) {}
  ArrayishObjectIterator(Arr& arr, size_t size) : _arr(arr),
  _index(0), _size(size) {}
  inline bool hasNext() { return _index<_size; }
  inline ELEMENT_TYPE(Arr) next() { ASS(_index<_size); return _arr[_index++]; }
  inline bool knowsSize() { return true;}
  inline bool size() { return _size;}
private:
  Arr& _arr;
  size_t _index;
  size_t _size;
};

template<typename T>
class PointerIterator
{
public:
  DECL_ELEMENT_TYPE(T);
  inline PointerIterator(T* first, T* afterLast) :
    _curr(first), _afterLast(afterLast) {}
  inline bool hasNext() { ASS(_curr<=_afterLast); return _curr!=_afterLast; }
  inline T next() { ASS(hasNext()); return *(_curr++); }
private:
  T* _curr;
  T* _afterLast;
};

template<typename T>
class PointerPtrIterator
{
public:
  DECL_ELEMENT_TYPE(T*);
  inline PointerPtrIterator(T* first, T* afterLast) :
    _curr(first), _afterLast(afterLast) {}
  inline bool hasNext() { ASS(_curr<=_afterLast); return _curr!=_afterLast; }
  inline T* next() { ASS(hasNext()); return _curr++; }
private:
  T* _curr;
  T* _afterLast;
};


/**
 * Implementation object for VirtualIterator, that represents
 * an iterator that yields only one object.
 */
template<typename T>
class SingletonIterator
{
public:
  DECL_ELEMENT_TYPE(T);
  explicit SingletonIterator(T el) : _finished(false), _el(el) {}
  inline bool hasNext() { return !_finished; };
  inline T next() { ASS(!_finished); _finished=true; return _el; };
  inline bool knowsSize() const { return true; }
  inline size_t size() const { return 1; }
private:
  bool _finished;
  T _el;
};

template<typename T>
inline
SingletonIterator<T> getSingletonIterator(T el)
{
  return SingletonIterator<T>(el);
}

/**
 * Implementation object for VirtualIterator, that can casts objects
 * of its inner iterator to target type with static_cast.
 */
template<typename To, class Inner>
class StaticCastIterator
{
public:
  DECL_ELEMENT_TYPE(To);
  explicit StaticCastIterator(Inner inn) :_inn(inn) {}
  inline bool hasNext() { return _inn.hasNext(); };
  inline To next() { return static_cast<To>(_inn.next()); };
private:
  Inner _inn;
};

template<typename To, class Inner>
inline
StaticCastIterator<To,Inner> getStaticCastIterator(Inner it)
{
  return StaticCastIterator<To,Inner>(it);
}

struct NonzeroFn
{
  DECL_RETURN_TYPE(bool);
  template<typename T>
  bool operator()(T obj)
  {
    return obj!=0;
  }
};

template<typename T>
struct NonequalFn
{
  NonequalFn(T forbidden) : _forbidden(forbidden) {}
  DECL_RETURN_TYPE(bool);
  bool operator()(T obj)
  {
    return obj!=_forbidden;
  }
  T _forbidden;
};

template<typename T>
NonequalFn<T> getNonequalFn(T forbidden)
{
  return NonequalFn<T>(forbidden);
}

/**
 * A meta-iterator that yields only those elements of
 * underlying iterator, for which @b func(element)
 * returns true.
 */
template<class Inner, class Functor>
class FilteredIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Inner));

  FilteredIterator(Inner inn, Functor func)
  : _func(func), _inn(inn), _nextStored(false) {}
  bool hasNext()
  {
    if(_nextStored) {
      return true;
    }
    while(_inn.hasNext()) {
      _next=_inn.next();
      if(_func(_next)) {
	_nextStored=true;
	return true;
      }
    }
    return false;
  };
  OWN_ELEMENT_TYPE next()
  {
    if(!_nextStored) {
      ALWAYS(hasNext());
      ASS(_nextStored);
    }
    _nextStored=false;
    return _next;
  };
private:
  Functor _func;
  Inner _inn;
  OWN_ELEMENT_TYPE _next;
  bool _nextStored;
};

/**
 * Return meta-iterator that yields only those elements of
 * iterator @b inn, for which @b func(element) returns true.
 */
template<class Inner, class Functor>
inline
FilteredIterator<Inner,Functor> getFilteredIterator(Inner inn, Functor func)
{
  return FilteredIterator<Inner,Functor>(inn, func);
}


/**
 * A meta-iterator that yields elements of underlying iterator
 * only until @b func(element) returns false for some element.
 */
template<class Inner, class Functor>
class WhileLimitedIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Inner));
  WhileLimitedIterator(Inner inn, Functor func)
  : _func(func), _inn(inn), _nextStored(false) {}
  bool hasNext()
  {
    if(!_nextStored) {
      if(!_inn.hasNext()) {
        return false;
      }
      _next=_inn.next();
      _nextStored=true;
    }
    return _func(_next);
  };
  OWN_ELEMENT_TYPE next()
  {
    if(!_nextStored) {
      ALWAYS(hasNext());
      ASS(_nextStored);
    }
    _nextStored=false;
    return _next;
  };
private:
  Functor _func;
  Inner _inn;
  OWN_ELEMENT_TYPE _next;
  bool _nextStored;
};

/**
 * Return meta-iterator that yields elements of iterator @b inn
 * only until @b func(element) returns false for some element.
 */
template<class Inner, class Functor>
inline
WhileLimitedIterator<Inner,Functor> getWhileLimitedIterator(Inner inn, Functor func)
{
  return WhileLimitedIterator<Inner,Functor>(inn, func);
}


/**
 * Implementation object for VirtualIterator, that concatenates
 * two other virtual iterators.
 *
 * After the first iterator is empty, pointer to its core is dropped,
 * so that its resources can be released.
 */
template<class It1,class It2>
class CatIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(It1));

  CatIterator(It1 it1, It2 it2)
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
  OWN_ELEMENT_TYPE next()
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
  It1 _it1;
  It2 _it2;
};

template<class It1,class It2>
inline
CatIterator<It1,It2> getConcatenatedIterator(It1 it1, It2 it2)
{
  return CatIterator<It1,It2>(it1, it2);
}



/**
 * Implementation object for VirtualIterator, that yields elements
 * of its inner iterator transformed by specified functor.
 */
template<typename Inner, typename Functor>
class MappingIterator
{
public:
  DECL_ELEMENT_TYPE(RETURN_TYPE(Functor));
  explicit MappingIterator(Inner inner, Functor func)
  : _func(func), _inner(inner) {}
  inline bool hasNext() { return _inner.hasNext(); };
  inline RETURN_TYPE(Functor) next() { return _func(_inner.next()); };

  inline bool knowsSize() const { return _inner.knowsSize(); }
  inline size_t size() const { return _inner.size(); }
private:
  Functor _func;
  Inner _inner;
};

template<typename Inner, typename Functor>
MappingIterator<Inner,Functor> getMappingIterator(Inner it, Functor f)
{
  return MappingIterator<Inner,Functor>(it, f);
}


/**
 * Implementation object for VirtualIterator, that yields elements
 * created by Constructor with parameter from its inner iterator.
 */
template<typename Constructor, typename Inner>
class ConstructingIterator
{
public:
  DECL_ELEMENT_TYPE(Constructor*);
  explicit ConstructingIterator(Inner inner)
  : _inner(inner) {}
  inline bool hasNext() { return _inner.hasNext(); };
  inline Constructor* next() { return new Constructor(_inner.next()); };
private:
  Inner _inner;
};

template<typename Constructor, typename Inner>
inline
ConstructingIterator<Constructor,Inner> getConstructingIterator(Inner it)
{
  return ConstructingIterator<Constructor,Inner>(it);
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
template<typename Master>
class FlatteningIterator
{
public:
  typedef ELEMENT_TYPE(Master) Inner;
  typedef ELEMENT_TYPE(Inner) T;
  DECL_ELEMENT_TYPE(T);

  explicit FlatteningIterator(Master master)
  : _master(master)
  {
    if(_master.hasNext()) {
      _current=_master.next();
      _empty=false;
    } else {
      _empty=true;
    }
  }
  bool hasNext()
  {
    CALL("FlatteningIterator::hasNext");
    if(_empty) {
      return false;
    }
    for(;;) {
      if(_current.hasNext()) {
	return true;
      }
      if(!_master.hasNext()) {
	return false;
      }
      _current=_master.next();
    }
  }
  inline
  T next()
  {
    ASS(_current.hasNext());
    return _current.next();
  }
private:
  bool _empty;
  Master _master;
  Inner _current;
};

template<typename T>
class FlatteningIterator<VirtualIterator<VirtualIterator<T> > >
{
public:
  typedef VirtualIterator<T> Inner;
  typedef VirtualIterator<Inner> Master;
  DECL_ELEMENT_TYPE(T);

  explicit FlatteningIterator(Master master)
  : _master(master), _current(Inner::getEmpty()) {}
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
  inline
  T next()
  {
    ASS(_current.hasNext());
    return _current.next();
  }
private:
  Master _master;
  Inner _current;
};

template<typename T>
inline
FlatteningIterator<T> getFlattenedIterator(T it)
{
  return FlatteningIterator<T>(it);
}

template<typename Inner, typename Functor>
inline
FlatteningIterator<MappingIterator<Inner,Functor> > getMapAndFlattenIterator(Inner it, Functor f)
{
  return FlatteningIterator<MappingIterator<Inner,Functor> >(
	  MappingIterator<Inner,Functor>(it, f) );
}


template<class Inner>
class PersistentIterator
: public IteratorCore<ELEMENT_TYPE(Inner)>
{
public:
  typedef ELEMENT_TYPE(Inner) T;
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
  inline bool hasNext() { return _items; };
  inline
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
template<class Inner>
inline
VirtualIterator<ELEMENT_TYPE(Inner)> getPersistentIterator(Inner it)
{
  return vi( new PersistentIterator<Inner>(it) );
}


template<class Inner>
class UniquePersistentIterator
: public IteratorCore<ELEMENT_TYPE(Inner)>
{
public:
  typedef ELEMENT_TYPE(Inner) T;
  typedef Set<T> ItemSet;

  explicit UniquePersistentIterator(Inner& inn)
  {
    while(inn.hasNext()) {
      _items.insert(inn.next());
    }
    _iit=typename ItemSet::Iterator(_items);
  }
  inline bool hasNext() { return _iit.hasNext(); };
  inline
  T next()
  {
    return _iit.next();
  };
  inline bool knowsSize() const { return true; }
  inline size_t size() const { return _items.numberOfElements(); }
private:
  ItemSet _items;
  typename ItemSet::Iterator _iit;
};

/**
 * Return iterator, that yields unique values yielded by @b it.
 * Those values are yielded in arbitrary order.
 *
 * @b it object is used only during initialization.
 */
template<class Inner>
inline
VirtualIterator<ELEMENT_TYPE(Inner)> getUniquePersistentIterator(Inner it)
{
  if(!it.hasNext()) {
    return VirtualIterator<ELEMENT_TYPE(Inner)>::getEmpty();
  }
  return vi( new UniquePersistentIterator<Inner>(it) );
}
template<class Inner>
inline
VirtualIterator<ELEMENT_TYPE(Inner)> getUniquePersistentIteratorFromPtr(Inner* it)
{
  if(!it->hasNext()) {
    return VirtualIterator<ELEMENT_TYPE(Inner)>::getEmpty();
  }
  return vi( new UniquePersistentIterator<Inner>(*it) );
}


template<typename T>
class RangeIterator
{
public:
  DECL_ELEMENT_TYPE(T);
  inline
  RangeIterator(T from, T to)
  : _next(from), _from(from), _to(to) {}
  inline bool hasNext() { return _next<_to; };
  inline T next() { return _next++; };
  inline bool knowsSize() const { return true; }
  inline size_t size() const { return (_to>_from) ? (_to-_from) : 0; }
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
RangeIterator<T> getRangeIterator(T from, T to)
{
  return RangeIterator<T>(from, to);
}

template<typename T>
class CombinationIterator
{
public:
  DECL_ELEMENT_TYPE(pair<T,T>);
  CombinationIterator(T from, T to)
  : _first(from), _second(from), _afterLast(to)
  {
    ASS_LE(from,to);
    if(from!=to) {
      if(from+1==to) {
	_second=_afterLast;
      } else {
	moveToNext();
      }
    }
  }
  inline bool hasNext()
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
 * Return iterator, that yields all unordered pairs from set {@b from,
 * (@b from)+1, (@b from)+2,..., (@b to)-1}. (The addition is performed
 * by the operator++.) For a singleton set, nothing is yielded.
 */
template<typename T>
inline
CombinationIterator<T> getCombinationIterator(T from, T to)
{
  return CombinationIterator<T>(from, to);
}

template<typename T>
class Combination2Iterator
{
public:
  DECL_ELEMENT_TYPE(pair<T,T>);
  Combination2Iterator(T from, T to1, T to2)
  : _first(from), _second(from), _afterLast1(to1), _afterLast2(to2)
  {
    ASS_LE(from,to1);
    ASS_LE(to1,to2);
    if(from!=to1) {
      moveToNext();
    }
  }
  inline bool hasNext()
  { return _first!=_afterLast1 && _second!=_afterLast2; }
  pair<T,T> next()
  {
    ASS(hasNext());
    pair<T,T> res=pair<T,T>(_first,_second);
    ASS_LE(_first,_afterLast1);
    ASS_LE(_second,_afterLast2);
    moveToNext();
    return res;
  }
private:
  void moveToNext()
  {
    _second++;
    ASS_LE(_second,_afterLast2);
    if(_second==_afterLast2) {
      _first++;
      _second=_first;
      _second++;
      //now, if _second==_afterLast, there's no combination left
    }
  }
  T _first;
  T _second;
  T _afterLast1;
  T _afterLast2;
};

/**
 * Return iterator, that yields all unordered pairs from set {@b from,
 * (@b from)+1, (@b from)+2,..., (@b to2)-1} where one of the pair is
 * less than $b to1. (The addition is performed by the operator++.)
 * For a singleton set, nothing is yielded.
 *
 * Parameter @b to1 must be less than or equal to @b to2.
 */
template<typename T>
inline
Combination2Iterator<T> getCombinationIterator(T from, T to1, T to2)
{
  return Combination2Iterator<T>(from, to1, to2);
}


/**
 * Wraps a context around specified iterator.
 *
 * Context is an object of type @b Ctx with methods
 * bool enter(T)
 * void leave(T)
 * where @b T is the return type of inner iterator.
 * Method @b enter is called before an element of inner
 * iterator is yielded (with this element as a parameter).
 * If @b enter returns false, the element is skipped (@b leave is
 * not called for it).
 * @b leave is called when an element becomes no longer
 * needed (after the hasNext method is called next time,
 * or when the iterator is being destroyed).
 */
template<class Inner, class Ctx>
class ContextualIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Inner));

  ContextualIterator(Inner iit, Ctx context)
  : _inContext(false), _used(true), _context(context), _iit(iit) {}

  ~ContextualIterator()
  {
    assureContextLeft();
  }
  bool hasNext()
  {
    if(!_used) {
      return true;
    }
    assureContextLeft();
    do {
      if(!_iit.hasNext()) {
	return false;
      }
      _current=_iit.next();
    } while (!_context.enter(_current));
    _inContext=true;

    _used=false;
    return true;
  }
  inline
  ELEMENT_TYPE(Inner) next()
  {
    ASS(!_used);
    _used=true;
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
  bool _used;
  Ctx _context;
  Inner _iit;
  ELEMENT_TYPE(Inner) _current;
};

template<class Inner, class Ctx>
inline
ContextualIterator<Inner,Ctx> getContextualIterator(Inner it, Ctx context)
{
  return ContextualIterator<Inner,Ctx>(it, context);
}


///@}

}

#endif /* __Metaiterators__ */
