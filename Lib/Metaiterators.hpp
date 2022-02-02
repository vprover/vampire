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
 * @file Metaiterators.hpp
 * Defines class Metaiterators.
 */


#ifndef __Metaiterators__
#define __Metaiterators__

#include <utility>
#include <functional>

#include "Forwards.hpp"

#include "Lib/Recycler.hpp"
#include "List.hpp"
#include "DHSet.hpp"
#include "Recycler.hpp"
#include "VirtualIterator.hpp"
#include "TimeCounter.hpp"
#include "Lib/Option.hpp"

namespace Lib {

///@addtogroup Iterators
///@{


/**
 * Return iterator on the container C
 *
 * The getContentIterator method makes it possible to
 * iterate on arbitrary containers, provided the @b ITERATOR_TYPE
 * macro can obtain the iterator type of the container.
 *
 * For types where the use of the @b ITERATOR_TYPE macro is not
 * suitable, this method can be overloaded to obtain the
 * iterator by some other means.
 */
template<class C>
ITERATOR_TYPE(C) getContentIterator(C& c)
{
  return ITERATOR_TYPE(C)(c);
}

/**
 * Iterator class that iterates an array and never stops. This iterator
 * needs to be used e.g. inside a WhileLimitedIterator.
 */
template<class El>
class InfiniteArrayIterator
{
public:
  DECL_ELEMENT_TYPE(El);
  InfiniteArrayIterator(const El* ptr) : _nextPtr(ptr) {}
  inline bool hasNext() { return true; }
  inline OWN_ELEMENT_TYPE next() { return *(_nextPtr++); }
private:
  const El* _nextPtr;
};

template<class El>
InfiniteArrayIterator<El> getInfiniteArrayIterator(const El* ptr)
{
  CALL("getInfiniteArrayIterator");
  return InfiniteArrayIterator<El>(ptr);
}

template<class A> struct const_ref { using type = A const&; };
template<class A> struct mut_ref   { using type = A &; };
template<class A> struct no_ref    { using type = A; };
template<class A> using  const_ref_t = typename const_ref<A>::type; 
template<class A> using  mut_ref_t   = typename mut_ref<A>::type; 
template<class A> using  no_ref_t    = typename no_ref<A>::type; 

template<class Arr, template<class> class ref_t>
struct ArrayishContent { using type = ref_t<Arr>; };
template<class Arr> struct ArrayishContent<Arr, no_ref_t> { using type = Arr const&; };
template<class A, template<class> class ref_t> using  ArrayishContentType = typename ArrayishContent<A,ref_t>::type;

/** Iterator class for types whose elements are accessible by
 * @b operator[](size_t) with the first element at the index 0
 * and the others at consecutive indexes
 *
 * If the iterated object has a @b size() function, the single
 * argument constructor can be used. Otherwise the two parameter
 * constructor must be used, the second parameter being the size
 * of the container (so that the elements are at indexes 0, ...,
 * size-1) const.
 */
template<class Arr, template<class> class ref_t = no_ref_t>
class ArrayishObjectIterator
{
public:
  using Cont = ArrayishContentType<Arr, ref_t>;
  DECL_ELEMENT_TYPE(ref_t<ELEMENT_TYPE(Arr)>);
  ArrayishObjectIterator(Cont arr) : _arr(arr),
  _index(0), _size(_arr.size()) {}
  ArrayishObjectIterator(Cont arr, size_t size) : _arr(arr),
  _index(0), _size(size) {}
  inline bool hasNext() { return _index<_size; }
  inline ELEMENT_TYPE(ArrayishObjectIterator) next() { ASS(_index<_size); return _arr[_index++]; }
  inline bool knowsSize() { return true;}
  inline bool size() { return _size;}
private:
  Cont _arr;
  size_t _index;
  size_t _size;
};

template<template<class> class ref_t = no_ref_t, class Arr>
ArrayishObjectIterator<Arr, ref_t> getArrayishObjectIterator(Arr const& arr, size_t size)
{
  CALL("getArrayishObjectIterator");
  return ArrayishObjectIterator<Arr, ref_t>(arr, size);
}

template<template<class> class ref_t = no_ref_t, class Arr>
ArrayishObjectIterator<Arr, ref_t> getArrayishObjectIterator(Arr const& arr)
{ return ArrayishObjectIterator<Arr, ref_t>(arr); }


template<template<class> class ref_t = no_ref_t, class Arr>
ArrayishObjectIterator<Arr, ref_t> getArrayishObjectIterator(Arr& arr)
{ return ArrayishObjectIterator<Arr, ref_t>(arr); }

template<template<class> class ref_t = no_ref_t, class Arr>
ArrayishObjectIterator<Arr, ref_t> getArrayishObjectIterator(Arr& arr, size_t size)
{ return ArrayishObjectIterator<Arr, ref_t>(arr, size); }

template<class Arr>
class OwnedArrayishIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Arr));
  OwnedArrayishIterator(Arr&& arr) : _arr(std::move(arr)),
  _index(0), _size(_arr.size()) {}
  OwnedArrayishIterator(Arr&& arr, size_t size) : _arr(std::move(arr)),
  _index(0), _size(size) {}
  inline bool hasNext() { return _index<_size; }
  inline ELEMENT_TYPE(Arr) next() { ASS(_index<_size); return _arr[_index++]; }
  inline bool knowsSize() { return true;}
  inline bool size() { return _size;}
private:
  Arr _arr;
  size_t _index;
  size_t _size;
};

template<class Arr>
OwnedArrayishIterator<Arr> ownedArrayishIterator(Arr&& arr, size_t size)
{ return OwnedArrayishIterator<Arr>(std::move(arr), size); }

template<class Arr>
OwnedArrayishIterator<Arr> ownedArrayishIterator(Arr&& arr)
{ return OwnedArrayishIterator<Arr>(std::move(arr)); }


/**
 * Reads given number of values from an input stream.
 *
 * Assumes that the input stream has enough values for that!
 */
template<typename T>
class InputIterator
{
public:
  DECL_ELEMENT_TYPE(T);
  InputIterator(istream& inp, size_t cnt) : _inp(inp), _remaining(cnt) {}

  bool hasNext() const { return _remaining>0; }
  T next() {
    CALL("InputIterator::next");
    ASS_G(_remaining,0);
    _remaining--;
    T res;
    _inp >> res;
    return res;
  }

private:
  istream& _inp;
  size_t _remaining;
};

/**
 * Iterator class for pointers
 *
 * The constructor takes two arguments - a pointer to the first element,
 * and a pointer to the element after the last element to be returned.
 *
 * Consecutive elements are being obtained by the postfix @b operator++().
 */
template<typename T>
class PointerIterator
{
public:
  DECL_ELEMENT_TYPE(T);
  inline PointerIterator(const T* first, const T* afterLast) :
    _curr(first), _afterLast(afterLast) {}
  inline bool hasNext() { ASS(_curr<=_afterLast); return _curr!=_afterLast; }
  inline T next() { ASS(hasNext()); return *(_curr++); }
private:
  const T* _curr;
  const T* _afterLast;
};

/**
 * Iterator class for pointers returning pointers to elements
 *
 * The constructor takes two arguments - a pointer to the first element,
 * and a pointer to the element after the last element to be returned.
 *
 * Consecutive elements are being obtained by the postfix @b operator++().
 */
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
 * Iterator returning a single element
 *
 * The single element is being passed to the constructor of the iterator.
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

/**
 * Return iterator returning @b el as a single element
 *
 * @see SingletonIterator
 */
template<typename T>
inline
SingletonIterator<T> getSingletonIterator(T el)
{
  return SingletonIterator<T>(el);
}

/**
 * sequence of functions for creating tuple iterators
 */
template<typename T>
VirtualIterator<T> ti(T el)
{
  return pvi( getSingletonIterator(el) );
}

template<typename T>
VirtualIterator<T> ti(T el1, T el2)
{
  return pvi( getConcatenatedIterator(getSingletonIterator(el1),getSingletonIterator(el2)) );
}

template<typename T>
VirtualIterator<T> ti(T el1, T el2, T el3)
{
  return pvi( getConcatenatedIterator(getSingletonIterator(el1),
      getConcatenatedIterator(getSingletonIterator(el2),getSingletonIterator(el3))) );
}

/**
 * Iterator that can casts objects of its inner iterator to the target type
 * @b To with the static_cast operator
 *
 * @tparam To target type of the iterator
 * @tparam Inner type of the inner iterator
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

/**
 * Return an iterator that can casts objects of the iterator @b it to the target type
 * @b To
 *
 * @see StaticCastIterator
 */
template<typename To, class Inner>
inline
StaticCastIterator<To,Inner> getStaticCastIterator(Inner it)
{
  return StaticCastIterator<To,Inner>(it);
}


template <typename T>
struct identity
{
  typedef T type;
};
/**
 * A functor class that transforms a lambda object into a Functor with a return type
 * @author Giles
 */
template<typename Out,typename In>
struct Lambda
{
  Lambda(typename identity<std::function<Out(In)>>::type f) : _lambda(f) {}
  Out operator()(In obj){ return _lambda(obj); }
  std::function<Out(In)> _lambda;
};

template<typename T,typename S>
Lambda<T,S> lambda(std::function<T(S)> f){ return Lambda<T,S>(f); }

/**
 * A functor class that returns true if the argument is non-zero
 *
 * The nonzeroness is tested by @b x!=0 .
 */
struct NonzeroFn
{
  template<typename T>
  bool operator()(T obj)
  {
    return obj!=0;
  }
};

/**
 * A functor class that returns true if the argument is not equal
 * to a specified object
 *
 * The forbidded object is specified by the argument of the
 * object constructor.
 *
 * The nonequality is tested by the @b operator!=() .
 */
template<typename T>
struct NonequalFn
{
  NonequalFn(T forbidden) : _forbidden(forbidden) {}
  bool operator()(T obj)
  {
    return obj!=_forbidden;
  }
  T _forbidden;
};

/**
 * Return a functor object that checks for non-equality to the
 * @b forbidden object
 *
 * @see NonequalFn
 */
template<typename T>
NonequalFn<T> getNonequalFn(T forbidden)
{
  return NonequalFn<T>(forbidden);
}

/**
 * Iterator class that returns elements of the inner iterator
 * for which the functor returns true
 *
 * @tparam Inner type of the inner iterator
 * @tparam Functor type of the functor used for filtering the
 *   elements returned by the inner iterator
 */
template<class Inner, class Functor>
class FilteredIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Inner));

  FilteredIterator(Inner inn, Functor func)
  : _func(func), _inn(inn), _next() {}

  bool hasNext()
  {
    CALL("FilteredIterator::hasNext")
    if(_next.isSome()) {
      return true;
    }
    while(_inn.hasNext()) {
      auto next = _inn.next();
      if(_func(next)) {
        _next = Option<OWN_ELEMENT_TYPE>(std::move(next));
	return true;
      }
    }
    return false;
  };
  OWN_ELEMENT_TYPE next()
  {
    CALL("FilteredIterator::next")
    ALWAYS(hasNext());
    ASS(_next.isSome());
    auto out = std::move(_next).unwrap();
    _next = Option<OWN_ELEMENT_TYPE>();
    return out;
  };
private:
  
  Functor _func;
  Inner _inn;
  Option<OWN_ELEMENT_TYPE> _next;
};


/**
 * Iterator that maps the contents of another iterator by a function. Whenever the function retuns a non-empty Option
 * this iterator will return the corresponding value. 
 */
template<class Inner, class Functor>
class FilterMapIter
{
public:
  DECL_ELEMENT_TYPE(typename std::result_of<Functor(ELEMENT_TYPE(Inner))>::type::Content);

  FilterMapIter(Inner inn, Functor func)
  : _func(func), _inn(std::move(inn)), _next() {}

  bool hasNext()
  {
    CALL("FilterMapIter::hasNext")
    if(_next.isSome()) {
      return true;
    }
    while(_inn.hasNext()) {
      _next = _func(_inn.next());
      if(_next.isSome()) {
	return true;
      }
    }
    return false;
  };

  OWN_ELEMENT_TYPE next()
  {
    CALL("FilterMapIter::next")
    ALWAYS(hasNext());
    ASS(_next.isSome());
    auto out = std::move(_next).unwrap();
    _next = Option<OWN_ELEMENT_TYPE>();
    return out;
  };

private:
  Functor _func;
  Inner _inn;
  Option<OWN_ELEMENT_TYPE> _next;
};

template<class Inner, class Functor>
class FilteredDelIterator
{
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Inner));

  FilteredDelIterator(Inner inn, Functor func)
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
      } else {
        _inn.del();
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
 * Return an iterator object that returns elements of the @b inn iterator
 * for which the functor @b func returns true
 *
 * @see FilteredIterator
 */
template<class Inner, class Functor>
inline
FilteredIterator<Inner,Functor> getFilteredIterator(Inner inn, Functor func)
{
  return FilteredIterator<Inner,Functor>(inn, func);
}

template<class Inner, class Functor>
inline
FilteredDelIterator<Inner,Functor> getFilteredDelIterator(Inner inn, Functor func)
{
  return FilteredDelIterator<Inner,Functor>(inn, func);
}


/**
 * Iterator class that returns elements of an inner iterator
 * only until the specified functor returns false for some element
 * (this element is already not returned)
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
 * Return iterator object that returns elements of an inner iterator
 * @b inn only until the functor @b func returns false for some element
 * (this element is already not returned)
 *
 * @see WhileLimitedIterator
 */
template<class Inner, class Functor>
inline
WhileLimitedIterator<Inner,Functor> getWhileLimitedIterator(Inner inn, Functor func)
{
  return WhileLimitedIterator<Inner,Functor>(inn, func);
}


/**
 * Iterator that concatenates two other iterators
 *
 * The @b knowsSize() and @b size() functions of this iterator can be
 * called only if both underlying iterators contain these functions.
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

  /**
   * Return true the size of the iterator can be obtained
   *
   * This function can be called only if both underlying iterators contain
   * the @b knowsSize() function.
   */
  bool knowsSize() const { return _it1.knowsSize() && _it2.knowsSize(); }
  /**
   * Return the initial number of elements of this iterator
   *
   * This function can be called only if both underlying iterators contain
   * the @b size() function, and if the @b knowsSize() function returns true.
   */
  size_t size() const { return _it1.size()+_it2.size(); }
private:
  /** False if we have already iterated through the first iterator */
  bool _first;
  It1 _it1;
  It2 _it2;
};

/**
 * Return iterators @b it1 and @b it2 contatenated using object of
 * the @b CatIterator class
 *
 * @see CatIterator
 */
template<class It1,class It2>
inline
CatIterator<It1,It2> getConcatenatedIterator(It1 it1, It2 it2)
{
  return CatIterator<It1,It2>(it1, it2);
}



/**
 * Iterator that transforms elements of its inner iterator by
 * a specified functor
 *
 * The @b knowsSize() and @b size() functions of this iterator can be
 * called only if the underlying iterator contains these functions.
 */
template<typename Inner, typename Functor, typename ResultType=std::result_of_t<Functor(ELEMENT_TYPE(Inner))>>
class MappingIterator
{
public:
  DECL_ELEMENT_TYPE(ResultType);
  explicit MappingIterator(Inner inner, Functor func)
  : _func(func), _inner(std::move(inner)) {}
  inline bool hasNext() { CALL("MappingIterator::hasNext"); return _inner.hasNext(); };
  inline ResultType next() { return _func(_inner.next()); };

  /**
   * Return true the size of the iterator can be obtained
   *
   * This function can be called only if the underlying iterator contains
   * the @b knowsSize() function.
   */
  inline bool knowsSize() const { return _inner.knowsSize(); }
  /**
   * Return the initial number of elements of this iterator
   *
   * This function can be called only if the underlying iterator contains
   * the @b size() function, and if the @b knowsSize() function returns true.
   */
  inline size_t size() const { return _inner.size(); }
private:
  Functor _func;
  Inner _inner;
};


// /**
//  * Iterator that transforms elements of its inner iterator by
//  * a specified functor, that returns either a value or nothing. If nothing is returned 
//  * the iterator skips over the element
//  *
//  * The @b knowsSize() and @b size() functions of this iterator can be
//  * called only if the underlying iterator contains these functions.
//  */
// template<typename Inner, typename Functor>
// class FilterMappingIterator
// {
// public:
//   DECL_ELEMENT_TYPE(RETURN_TYPE(Functor(ELEMENT_TYPE(Inner)))::Inner);
//   explicit FilterMappingIterator(Inner inner, Functor func)
//   : _func(func), _inner(inner) {}
//   inline bool hasNext() { ASSERTION_VIOLATION };
//   inline ELEMENT_TYPE(FilterMappingIterator) next() { ASSERTION_VIOLATION };
//
//   /**
//    * Return true the size of the iterator can be obtained
//    *
//    * This function can be called only if the underlying iterator contains
//    * the @b knowsSize() function.
//    */
//   inline bool knowsSize() const { return _inner.knowsSize(); }
//   /**
//    * Return the initial number of elements of this iterator
//    *
//    * This function can be called only if the underlying iterator contains
//    * the @b size() function, and if the @b knowsSize() function returns true.
//    */
//   inline size_t size() const { return _inner.size(); }
// private:
//   Functor _func;
//   Inner _inner;
// };

/**
 * Return iterator that returns elements of @b it transformed by
 * the functor @b f
 *
 * @see MappingIterator
 */
template<typename Inner, typename Functor>
MappingIterator<Inner,Functor,std::result_of_t<Functor(ELEMENT_TYPE(Inner))>> getMappingIterator(Inner it, Functor f)
{
  return MappingIterator<Inner,Functor,std::result_of_t<Functor(ELEMENT_TYPE(Inner))>>(std::move(it), f);
}

// /**
//  * Return iterator that returns elements of @b it transformed by
//  * the lambda @b f
//  *
//  * @see MappingIterator
//  */
// template<typename Inner, typename Functor,typename ResultType>
// MappingIterator<Inner,Functor,ResultType> getMappingIterator(Inner it, std::function<ResultType(Inner)> f)
// {
//   return MappingIterator<Inner,Functor,ResultType>(it, f);
// }

/**
 * Return iterator that returns elements of @b it transformed by
 * the functor @b f
 *
 * @see MappingIterator
 */
template<typename ResultType, typename Inner, typename Functor>
MappingIterator<Inner,Functor,ResultType> getMappingIteratorKnownRes(Inner it, Functor f)
{
  return MappingIterator<Inner,Functor,ResultType>(it, f);
}


/**
 * Iterator that uses elements of its inner iterator as argments to
 * single-parameter constructor @b Constructor, and yields created
 * objects.
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

/**
 * Return iterator that uses elements of @b it as arguments to
 * the single-paramater constructor of type @b Constructor and
 * returns the created elements
 *
 * @see ConstructingIterator
 */
template<typename Constructor, typename Inner>
inline
ConstructingIterator<Constructor,Inner> getConstructingIterator(Inner it)
{
  return ConstructingIterator<Constructor,Inner>(it);
}


/**
 * Iterator that takes iterator over iterators as its argument and
 * flattens it, returning elements of the inner iterators.
 *
 * @tparam Master The outer iterator to be flattened. It must be
 *   an iterator over iterators, which also means that the macro
 *   @b ELEMENT_TYPE() must be applicable to the result of
 *   @b ELEMENT_TYPE(Master)
 */
template<typename Master>
class FlatteningIterator
{
public:
  using Inner = ELEMENT_TYPE(Master);
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Inner));

  explicit FlatteningIterator(Master master)
  : _master(std::move(master))
  , _current(std::move(_master.hasNext() 
        ? Option<Inner>(std::move(_master.next()))
        : Option<Inner>()))
  { }

  bool hasNext()
  {
    CALL("FlatteningIterator::hasNext");
    while (_current.isSome()) {
      if (_current.unwrap().hasNext()) {
        return true;
      } else {
        _current = std::move(_master.hasNext() 
            ? Option<Inner>(std::move(_master.next()))
            : Option<Inner>());
      }
    }
    return false;
  }

  inline
  ELEMENT_TYPE(FlatteningIterator) next()
  {
    CALL("FlatteningIterator::next");
    ASS(_current.isSome());
    ASS(_current.unwrap().hasNext());
    return _current.unwrap().next();
  }
private:
  Master _master;
  Option<Inner> _current;
};

/**
 * Return iterator that flattens the iterator over iterators @b it
 * into an iterator over elements the inner elements
 *
 * @b it must be an iterator over iterators
 *
 * @see FlatteningIterator, FlatteningIterator<VirtualIterator<VirtualIterator<T>>>
 */
template<typename T>
inline
FlatteningIterator<T> getFlattenedIterator(T it)
{ return FlatteningIterator<T>(std::move(it)); }

template<class Inner, class Functor>
using FlatMapIter = FlatteningIterator<MappingIterator<Inner,Functor>>;

/**
 * Return iterator that applies functor @b f to elements of the @b it
 * iterator, treats the result as iterators and flattens them
 *
 * This function is a combination of the @b getMappingIterator() and
 * @b getFlattenedIterator() functions.
 *
 * The functor @b f must return an iterator
 *
 * @see getMappingIterator(), getFlattenedIterator()
 */
template<typename Inner, typename Functor>
inline
FlatMapIter<Inner,Functor> getMapAndFlattenIterator(Inner it, Functor f)
{
  return FlatteningIterator<MappingIterator<Inner,Functor> >(
	  MappingIterator<Inner,Functor>(std::move(it), f) );
}

/**
 * Iterator that in its constructor stores elements of an inner iterator
 * and then returns these elements later in the same order
 *
 * The iterator object does not contain the copy constructor or
 * the operator=. If this behavior is required, it should be created
 * on the heap and pointer to it put inside a VirtualIterator object.
 *
 * This iterator should be used when a resource held by an iterator
 * needs to be released before the elements of the iterator are required.
 *
 * @see VirtualIterator
 */
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
      List<T>::destroy(_items);
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
 * Return iterator that stores values of @b it in its constructor,
 * and then yields them in the same order
 *
 * After the call to this function, the iterator @b it and any resources
 * it holds may be released, since the elements are stored independently
 * of it.
 *
 * @see PersistentIterator
 */
template<class Inner>
inline
VirtualIterator<ELEMENT_TYPE(Inner)> getPersistentIterator(Inner it)
{
  return vi( new PersistentIterator<Inner>(it) );
}


/**
 * Iterator that in its constructor stores elements of an inner iterator
 * and then returns these elements later in a deterministic order, skipping
 * the duplicate ones
 *
 * The iterator object does not contain the copy constructor or
 * the operator=. If this behavior is required, it should be created
 * on the heap and pointer to it put inside a VirtualIterator object.
 *
 * @see VirtualIterator
 */
template<class Inner>
class UniquePersistentIterator
: public IteratorCore<ELEMENT_TYPE(Inner)>
{
public:
  typedef ELEMENT_TYPE(Inner) T;
private:
  typedef List<T> ItemList;
public:

  explicit UniquePersistentIterator(Inner& inn)
  {
    _items=getUniqueItemList(inn, _size);
  }
  ~UniquePersistentIterator()
  {
    if(_items) {
      ItemList::destroy(_items);
    }
  }
  inline bool hasNext() { return _items; };
  inline T next()
  {
    return ItemList::pop(_items);
  };

  inline bool knowsSize() const { return true; }
  inline size_t size() const { return _size; }
private:
  typedef DHSet<T> ItemSet;

  static ItemList* getUniqueItemList(Inner& inn, size_t& sizeRef)
  {
    CALL("UniquePersistentIterator::getUniqueItemList");

    ItemList* res=0;
    ItemSet* iset;
    Recycler::get(iset);
    iset->reset();

    sizeRef=0;
    while(inn.hasNext()) {
      T el=inn.next();
      if(iset->insert(el)) {
	ItemList::push(el, res);
	sizeRef++;
      }
    }

    Recycler::release(iset);
    return res;
  }

  ItemList* _items;
  size_t _size;
};

/**
 * Return iterator that stores values of @b it in its constructor,
 * and then yields them in a deterministic order, skipping duplicate values
 *
 * After the call to this function, the iterator @b it and any resources
 * it holds may be released, since the elements are stored independently
 * of it.
 *
 * @see UniquePersistentIterator
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

/**
 * Return iterator that stores values of the iterator pointed to by @b it
 * in its constructor, and then yields them in a deterministic order,
 * skipping duplicate values
 *
 * After the call to this function, the iterator pointed to by @b it and
 * any resources it holds may be released, since the elements are stored
 * independently of it.
 *
 * @see UniquePersistentIterator
 */
template<class Inner>
inline
VirtualIterator<ELEMENT_TYPE(Inner)> getUniquePersistentIteratorFromPtr(Inner* it)
{
  if(!it->hasNext()) {
    return VirtualIterator<ELEMENT_TYPE(Inner)>::getEmpty();
  }
  return vi( new UniquePersistentIterator<Inner>(*it) );
}

/**
 * Remove duplicate elements from the container @c cont
 */
template<class Container>
void makeUnique(Container& cont)
{
  CALL("makeUnique");

  VirtualIterator<ELEMENT_TYPE(Container)> uniqueIt = pvi(
      getUniquePersistentIterator(ITERATOR_TYPE(Container)(cont)) );
  cont.reset();
  cont.loadFromIterator(uniqueIt);
}

/**
 * Return number of elements in iterator @c it
 */
template<class It>
size_t countIteratorElements(It it)
{
  CALL("countIteratorElements");

  size_t res = 0;
  while(it.hasNext()) {
    it.next();
    res++;
  }
  return res;
}


/**
 * Iterator that goes from object @b from to the object @b to using the
 * postfix @b operator++. (The objects are passed in the constructor.)
 * The object @b to is not returned.
 */
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
 * Return iterator that goes from object @b from to the object @b to
 * using the postfix @b operator++; the object @b to is not returned
 *
 * @see RangeIterator
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
 * less than @b to1. (The addition is performed by the operator++.)
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


template<class Inner>
class TimeCountedIterator
: public IteratorCore<ELEMENT_TYPE(Inner)>
{
public:
  typedef ELEMENT_TYPE(Inner) T;

  explicit TimeCountedIterator(Inner inn, TimeCounterUnit tcu)
  : _inn(inn), _tcu(tcu) {}

  inline bool hasNext()
  {
    TimeCounter tc(_tcu);
    return _inn.hasNext();
  };
  inline
  T next()
  {
    TimeCounter tc(_tcu);
    return _inn.next();
  };
private:
  Inner _inn;
  TimeCounterUnit _tcu;
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
VirtualIterator<ELEMENT_TYPE(Inner)> getTimeCountedIterator(Inner it, TimeCounterUnit tcu)
{
  return vi( new TimeCountedIterator<Inner>(it, tcu) );
}

/**
 * Return true iff @c it1 and it2 contain the same values in the same order
 */
template<class It1, class It2>
bool iteratorsEqual(It1 it1, It2 it2)
{
  CALL("iteratorsEqual");

  while(it1.hasNext()) {
    if(!it2.hasNext()) {
      return false;
    }
    if(it1.next()!=it2.next()) {
      return false;
    }
  }
  return !it2.hasNext();
}

template<typename T>
static bool lessThan(T a, T b) { return a<b; }

/**
 * Return true iff @c it is sorted according to the default < ordering
 * (each element is less than its successive element).
 */
template<class It>
bool isSorted(It it)
{
  CALL("isSorted/1");

  if(!it.hasNext()) { return true; }

  ELEMENT_TYPE(It) prev = it.next();

  while(it.hasNext()) {
    ELEMENT_TYPE(It) curr = it.next();
    if(!(prev<curr)) {
      return false;
    }
    prev = curr;
  }
  return true;
}

/**
 * Return true iff @c it is sorted according to ordering specified by lessThan
 * (each element is less than its successive element).
 *
 * Transitivity of @c lessThan is assumed.
 */
template<class It, typename Pred>
bool isSorted(It it, Pred lessThan)
{
  CALL("isSorted/2");

  if(!it.hasNext()) { return true; }

  ELEMENT_TYPE(It) prev = it.next();

  while(it.hasNext()) {
    ELEMENT_TYPE(It) curr = it.next();
    if(!lessThan(prev, curr)) {
      return false;
    }
    prev = curr;
  }
  return true;
}

/**
 * Return true iff pred returns true for all elements of it
 */
template<class It, typename Pred>
bool forAll(It it, Pred pred)
{
  CALL("forAll");

  while(it.hasNext()) {
    if(!pred(it.next())) {
      return false;
    }
  }
  return true;
}

/**
 * Return first element for which pred returns true.
 * There must be an element for which true is returned in the iterator.
 */
template<class It, typename Pred>
ELEMENT_TYPE(It) getFirstTrue(It it, Pred pred)
{
  CALL("getFirstTrue");

  while(it.hasNext()) {
    ELEMENT_TYPE(It) el = it.next();
    if(pred(el)) {
      return el;
    }
  }
  ASSERTION_VIOLATION;
}

/**
 * Do folding on iterator it using fn which is a function taking
 * iterator element as first argument and the intermediate result
 * as the second.
 */
template<class It, typename Fun, typename Res>
Res fold(It it, Fun fn, Res init)
{
  CALL("fold/3");
  Res res = init;
  while(it.hasNext()) {
    res = fn(it.next(), res);
  }
  return res;
}

/**
 * Do folding on iterator it using fn which is a function taking
 * iterator element as first argument and the intermediate result
 * as the second.
 * it must be a non-empty iterator.
 */
template<class It, typename Fun>
ELEMENT_TYPE(It) fold(It it, Fun fn)
{
  CALL("fold/2");

  ALWAYS(it.hasNext());
  ELEMENT_TYPE(It) init = it.next();
  return fold(it,fn,init);
}

/** sum function, useful for fold */
template<typename T>
T sumFn(T a1, T a2) { return a1+a2; }

/** max function, useful for fold */
template<typename T>
T maxFn(T a1, T a2) { return max(a1,a2); }

/** min function, useful for fold */
template<typename T>
T minFn(T a1, T a2) { return min(a1,a2); }


template<class It>
struct StmJoinAuxStruct
{
  StmJoinAuxStruct(vstring glue, It it) : _glue(glue), _it(it) {}
  vstring _glue;
  It _it;
};

template<class It>
StmJoinAuxStruct<It> join(vstring glue, It it)
{
  return StmJoinAuxStruct<It>(glue, it);
}
template<typename It>
std::ostream& operator<< (ostream& out, const StmJoinAuxStruct<It>& info )
{
  It it = info._it;
  while(it.hasNext()) {
    out << it.next();
    if(it.hasNext()) {
      out << info._glue;
    }
  }
  return out;
}


/**
 * Split iterator @c it into two iterators in the element satisfying
 * the @c edge predicate. If there is no element satisfying @c edge,
 * return false, put the original iterator into res1 and make res2 empty.
 * The first element for which edge succeeded is not present in any
 * of the resulting iterators.
 */
template<class It, class Pred>
bool splitIterator(It it, Pred edge, VirtualIterator<ELEMENT_TYPE(It)>& res1, VirtualIterator<ELEMENT_TYPE(It)>& res2)
{
  CALL("splitIterator");

  typedef ELEMENT_TYPE(It) T;

  bool success = false;
  List<T>* firstPart = 0;
  while(it.hasNext()) {
    T itm = it.next();
    if(edge(itm)) {
      success = true;
      break;
    }
    List<T>::push(itm, firstPart);
  }
  firstPart = firstPart->reverse();
  res1 = fpvi(typename List<T>::DestructiveIterator(firstPart));
  res2 = pvi(it);
  return success;
}

template<typename Inner>
struct NegPred
{
  NegPred(const Inner& inner) : _inner(inner) {}
  template<typename Arg>
  bool operator()(Arg a) { return !_inner(a); }
private:
  Inner _inner;
};

template<typename Inner>
NegPred<Inner> negPred(Inner inner) {
  return NegPred<Inner>(inner);
}

template<typename T>
struct ConstEqPred
{
  ConstEqPred(const T& val) : _val(val) {}
  template<typename Arg>
  bool operator()(Arg a) { return a==_val; }
private:
  T _val;
};

template<typename T>
ConstEqPred<T> constEqPred(const T& val) {
  return ConstEqPred<T>(val);
}

template<typename OuterFn, typename InnerFn>
struct CompositionFn {
  CompositionFn(OuterFn outer, InnerFn inner)
   : _outer(outer), _inner(inner) { }

  template<typename Arg>
  std::result_of_t<OuterFn(std::result_of_t<InnerFn(Arg)>)> operator()(Arg a) {
    return _outer(_inner(a));
  }
private:
  OuterFn _outer;
  InnerFn _inner;
};

template<typename OuterFn, typename InnerFn>
CompositionFn<OuterFn,InnerFn> getCompositionFn(OuterFn outer, InnerFn inner)
{
  CALL("getCompositionFn");
  return CompositionFn<OuterFn,InnerFn>(outer,inner);
}

template<class P>
struct GetFirstOfPair {
  typename P::first_type operator()(P p) {
    return p.first;
  }
};

template<class P>
struct GetSecondOfPair {
  typename P::second_type operator()(P p) {
    return p.second;
  }
};

template<class Iter>
class IterTraits
{
  Iter _iter;
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Iter));
  using Elem = ELEMENT_TYPE(Iter);

  explicit IterTraits(Iter iter) : _iter(std::move(iter)) {}

  Elem next() 
  { 
    CALL("IterTraits::next")
    return _iter.next(); 
  }

  bool hasNext() 
  { 
    CALL("IterTraits::hasNext")
    return _iter.hasNext(); 
  }

  Option<Elem> tryNext() 
  { 
    return _iter.hasNext() 
        ? Option<Elem>(_iter.next())
        : Option<Elem>();
  }


  template<class P>
  bool any(P f) 
  {
    CALL("IterTraits::any")
    while (hasNext()) {
      if (f(next())) return true;
    }
    return false;
  }

  template<class P>
  bool all(P f) 
  {
    CALL("IterTraits::all")
    while (hasNext()) {
      if (!f(next())) return false;
    }
    return true;
  }

  template<class F>
  void forEach(F f) 
  {
    CALL("IterTraits::forEach")
    while (hasNext()) {
      f(next());
    }
  }

  template<class P>
  Option<Elem> find(P p) 
  {
    CALL("IterTraits::find")
    while (hasNext()) {
      Elem x = next();
      if (p(x)) {
        return some<Elem>(x);
      }
    }
    return none<Elem>();
  }

  template<class P>
  Option<unsigned> findPosition(P p) 
  {
    CALL("IterTraits::findPosition")
    unsigned i = 0;
    while (hasNext()) {
      Elem x = next();
      if (p(x)) {
        return some<unsigned>(i);
      }
      i++;
    }
    return none<unsigned>();
  }

  template<class F>
  IterTraits<MappingIterator<Iter, F>> map(F f)
  { return iterTraits(getMappingIterator<Iter, F>(std::move(_iter), f)); }

  template<class F>
  IterTraits<FilteredIterator<Iter, F>> filter(F f)
  { return iterTraits(getFilteredIterator<Iter, F>(std::move(_iter), f)); }

  template<class F>
  IterTraits<FilterMapIter<Iter, F>> filterMap(F f)
  { return iterTraits(FilterMapIter<Iter, F>(std::move(_iter), f)); }

  template<class F>
  IterTraits<FlatMapIter<Iter, F>> flatMap(F f)
  { return iterTraits(getFlattenedIterator(getMappingIterator(std::move(_iter), f))); }


  Option<Elem> min()
  { 
    CALL("IterTraits::min")
    if (hasNext()) {
      auto&& min = next();
      while (hasNext())  {
        auto&& e = next();
        if (std::less<Elem>{}(e, min)) {
          min = e;
        }
      }
      return some<Elem>(min);
    } else {
      return none<Elem>();
    }
  }


  template<class Container>
  Container collect()
  { 
    CALL("IterTraits::collect/1")
    return Container::fromIterator(*this); 
  }
  

  template<template<class> class Container>
  Container<Elem> collect()
  { 
    CALL("IterTraits::collect/2")
    return Container<Elem>::fromIterator(*this); 
  }
  
  /** This class is to be used in the context of a for (auto x : ...) loop only. */
  class StlIter 
  {
    Option<IterTraits&> _iter; // <- nothing here encodes that this == end()
    Option<Elem>  _cur;

  public:
    StlIter(IterTraits& iter)  : _iter(Option<IterTraits&>(iter)), _cur(std::move(iter.tryNext())) {}
    StlIter()  : _iter(), _cur() {}

    void operator++() 
    { _cur = _iter.unwrap().tryNext(); }

    Elem operator*() 
    { return _cur.unwrap(); } 

    friend bool operator!=(StlIter const& lhs, StlIter const& rhs) 
    { return !(lhs == rhs); }

    friend bool operator==(StlIter const& lhs, StlIter const& rhs) 
    { 
      ASS(rhs._iter.isNone()); 
      ASS(lhs._iter.isSome()); 
      return lhs._cur.isNone(); 
    }

  };

public:
  StlIter begin() { return StlIter(*this); }
  StlIter end() { return StlIter(); }

};

template<class Iter>
IterTraits<Iter> iterTraits(Iter i) 
{ return IterTraits<Iter>(std::move(i)); }

///@}

}

#endif /* __Metaiterators__ */
