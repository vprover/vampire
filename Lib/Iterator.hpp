/*
 * File Iterator.hpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */


#ifndef __LIB__ITERATOR__HPP__
#define __LIB__ITERATOR__HPP__

#include <type_traits>
#include "Lib/Reflection.hpp" // <-- TODO remove this
#include "Lib/TypeList.hpp"
#include "Lib/Option.hpp"


namespace Lib {
namespace Iterator {


template<class Iter>
using ElemT = ELEMENT_TYPE(Iter);

template<class Iter>
struct is_iterator 
{ 
  static constexpr bool value = 
    std::is_same<decltype(((Iter*)nullptr)->sizeLeft()), Option<unsigned>>::value &&
    std::is_same<decltype(((Iter*)nullptr)-> hasNext()), bool>::value &&
    std::is_same<decltype(((Iter*)nullptr)->    next()), ElemT<Iter>>::value;
};

#define ASSERT_ITERATOR(...) \
  static_assert(is_iterator<__VA_ARGS__>::value, "not an iterator type")

template<class Iter, class Adaptor>
typename std::result_of<Adaptor(Iter)>::type operator|(Iter iter, Adaptor adaptor) 
{ 
  ASSERT_ITERATOR(Iter);
  return adaptor(iter); 
}


///////////////////////////////////////////////////////////////////////////////////////
// BASE ITERATORS
//////////////////////

template<class E>
class DynIterator 
{
public:
  DECL_ELEMENT_TYPE(E);
  virtual E next();
  virtual bool hasNext();
  virtual Option<unsigned> sizeLeft();
  ASSERT_ITERATOR(DynIterator);
};

template<class T> T&& fwd(typename std::remove_reference<T>::type&  t) { return std::forward<T>(t); }
template<class T> T&& fwd(typename std::remove_reference<T>::type&& t) { return std::forward<T>(t); }
template<class T> T&& fwd(typename std::remove_reference<T>::type   t) { return std::move<T>(t); }

/** Iterator for any object that implements the indexing operator */
template<class Array, class Idx = unsigned>
class IndexIter {
  Idx _idx;
  Idx _size;
  Array _array;
public:
  DECL_ELEMENT_TYPE(decltype(_array[_idx]));
  IndexIter(Array array, Idx size) : _array(fwd(array)), _idx(0), _size(_array.size()) {}
  IndexIter(Array array) : IndexIter(fwd(array), _array.size()) {}
  bool hasNext() { return _idx < _size; }
  ElemT<IndexIter> next() { return _array[_idx]; }
  Option<unsigned> sizeLeft() { return Option<unsigned>(_size - _idx); }
};

// TODO remove me
template<class Iter>
class IterWrapper {
  Iter _iter;
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Iter));
  IterWrapper(Iter iter) : _iter(std::move(iter)) {}
  bool hasNext() { return _iter.hasNext(); }
  ElemT<Iter> next() { return _iter.next(); }
  Option<unsigned> sizeLeft() { return 
    _iter.knownSize() ? Option<unsigned>(_iter.size())
                      : Option<unsigned>(); }
};

///////////////////////////////////////////////////////////////////////////////////////
// ITERATOR ADAPTORS
//////////////////////

using TypeList::List;
using TypeList::Indices;
using TypeList::UnsignedList;

template<template<class...> class C, class... Args>
class Adaptor 
{ 
  std::tuple<Args...> _args; 

public:
  Adaptor(Args... args) : _args(std::tuple<Args>(args)...) {}

  template<class Iter>
  C<Iter, Args...> operator()(Iter i) 
  { return apply(std::move(i), Indices<List<Args...>>{}); }

  template<class Iter, int ...idx>
  C<Iter, Args...> apply(Iter iter, UnsignedList<idx ...>)
  { return C<Iter, Args...>(std::move(iter), std::move(std::get<idx>(_args))...); }
};

namespace Adaptors {

namespace Map {

template<class Iter, class Func>
class Map 
{
  Iter _iter;
  Func _func;
public:
  using Result = typename std::result_of<Func(ElemT<Iter>)>::type;
  DECL_ELEMENT_TYPE(Result);
  Map(Iter inner, Func func) : _iter(std::move(inner)), _func(std::move(func)) {}
  inline bool hasNext() { return _iter.hasNext(); };
  inline Result next() { return _func(_iter.next()); }
  inline Option<unsigned> sizeLeft() { return _iter.sizeLeft(); }
};

template<class F>
Adaptor<Map, F> map(F f) 
{ return Adaptor<Map, F>(std::move(f)); }

} // namespace Map


namespace Filter {

template<class Iter, class Func>
class Filter 
{
  Func _func;
  Iter _inn;
  Option<ElemT<Iter>> _next;
public:
  DECL_ELEMENT_TYPE(ElemT<Iter>);

  Filter(Iter inn, Func func)
  : _func(func), _inn(inn), _next() {}

  bool hasNext()
  {
    CALL("Filter::hasNext")
    if(_next.isSome()) {
      return true;
    }
    while(_inn.hasNext()) {
      ElemT<Iter> next = _inn.next();
      if(_func(next)) {
        _next = Option<ElemT<Iter>>(std::move(next));
        return true;
      }
    }
    return false;
  };
  inline Option<unsigned> sizeLeft() { return Option<unsigned>(); }
  ElemT<Iter> next()
  {
    CALL("Filter::next")
    ALWAYS(hasNext());
    ASS(_next.isSome());
    ElemT<Iter> out = std::move(_next).unwrap();
    DBGE(out)
    _next = Option<ElemT<Iter>>();
    return out;
  };
};

template<class F>
Adaptor<Filter, F> filter(F f) 
{ return Adaptor<Filter, F>(std::move(f) ); }

} // namespace Filter


namespace Flatten {

template<typename Outer>
class Flatten
{
using Inner = ElemT<Outer>;
private:
Outer _master;
Option<Inner> _current;
public:
DECL_ELEMENT_TYPE(ElemT<Inner>);


explicit Flatten(Outer master)
: _master(std::move(master))
, _current(std::move(_master.hasNext() 
      ? Option<Inner>(std::move(_master.next()))
      : Option<Inner>()))
{ }

bool hasNext()
{
  CALL("Flatten::hasNext");
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

ElemT<Inner> next()
{
  CALL("Flatten::next");
  ASS(_current.isSome());
  ASS(_current.unwrap().hasNext());
  return _current.unwrap().next();
}

inline Option<unsigned> sizeLeft() 
{ return Option<unsigned>(); }
};

Adaptor<Flatten> flatten() 
{ return Adaptor<Flatten>(); }

} // namespace Flatten

namespace Cloned {

using Map::Map;

struct Clone {
  template<class A> A operator()(A const& val) { return A(val); }
  template<class A> A operator()(A      & val) { return A(val); }
  template<class A> A operator()(A     && val) { return A(val); }
};

Adaptor<Map, Clone> cloned() 
{ return Adaptor<Map, Clone>(Clone{}); }

} // namespace Cloned

namespace SizeHint {

template<class Iter, class Unsigned>
class SizeHint
{
  Iter _iter;
  unsigned _size;
public:
  DECL_ELEMENT_TYPE(ElemT<Iter>);


  SizeHint(Iter iter, Unsigned size) : _iter(iter) , _size(size) { }

  bool hasNext()
  { return _iter.hasNext(); }

  ElemT<Iter> next()
  { 
    ASS_G(_size, 0)
    _size--; 
    return _iter.next(); 
  }

  inline Option<unsigned> sizeLeft() 
  { return Option<unsigned>(_size); }
};

Adaptor<SizeHint, unsigned> sizeHint(unsigned size) 
{ return Adaptor<SizeHint, unsigned>(size); }

} // namespace SizeHint


namespace FlatMap {

template<class Iter, class F>
class FlatMap
{
  using SelfMap = Map::Map<Iter, F>;
  using Self = Flatten::Flatten<SelfMap>;
  Self _self;
public:
  DECL_ELEMENT_TYPE(ElemT<Self>);

  FlatMap(Iter i, F f) 
    : _self(Self(SelfMap(std::move(i), std::move(f)))) {}

  ElemT<Self> next()                 { return _self.next(); }
  bool hasNext()                     { return _self.hasNext(); }
  inline Option<unsigned> sizeLeft() { return _self.sizeLeft(); }
};

template<class F>
Adaptor<FlatMap, F> flatMap(F f) 
{ return Adaptor<FlatMap, F>(std::move(f)); }

} // namespace FlatMap

namespace ToStl {
  template<class Iter>
  Option<ElemT<Iter>> tryNext(Iter& iter)
  { return iter.hasNext() ? Option<ElemT<Iter>>(iter.next()) : Option<ElemT<Iter>>(); }

template<class Iter>
class Stl {
  Iter _iter;
  /** This class is to be used in the context of a for (auto x : ...) loop only. */
  class StlIter 
  {
    Option<Iter&> _iter; // <- nothing here encodes that this == end()
    Option<ElemT<Iter>>  _cur;

  public:
    StlIter(Iter& iter)  : _iter(Option<Iter&>(iter)), _cur(std::move(tryNext(iter))) {}
    StlIter()  : _iter(), _cur() {}

    void operator++() 
    { _cur = tryNext(_iter.unwrap()); }

    ElemT<Iter> operator*() 
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
  Stl(Iter iter) : _iter(std::move(iter)) {}

  StlIter begin() { return StlIter(_iter); }
  StlIter end() { return StlIter(); }
};

Adaptor<Stl> toStl()
{ return Adaptor<Stl>(); }

} // namespace ToStl

} // namespace Adaptors


///////////////////////////////////////////////////////////////////////////////////////
// ITERATOR DESTRUCTORS
//////////////////////

namespace Destructors {

/**
 * Collects all elements of the iterator into a container.
 * The container type needs to implement the function the function
 * template<class Iter> static C fromIterator(Iter);
 */
namespace Collect {

template<class Container>
class Collector { 
public:
  template<class Iter>
  Container operator()(Iter iter) 
  { return Container::fromIterator(iter); }
};

/** Collects the elemnts of an iterator into a container of type C */
template<class C>
Collector<C> collect()
{ return Collector<C>(); }

template<template<class> class Container>
class HkCollector { 
public:
  template<class Iter>
  Container<ElemT<Iter>> operator()(Iter iter) 
  { return Container<ElemT<Iter>>::fromIterator(iter); }
};


/** Collects the elemnts of an iterator into a container of a template type with one parameter. 
 * This parameter will be instantiated with the iterator element type. 
 * e.g.: collect<Stack>() will collect the elements of an iterator with elements of type int into a Stack<int>
 */
template<template<class> class C>
HkCollector<C> collect()
{ return HkCollector<C>(); }

} // namespace Collect


namespace ForEach {

template<class F>
class ForEach { 
  F _f;
public:
  ForEach(F f) : _f(f) {}
  template<class Iter>
  void operator()(Iter iter) 
  { 
    while (iter.hasNext()) {
      _f(iter.next());
    }
  }
};

template<class F>
ForEach<F> forEach(F f)
{ return ForEach<F>(f); }

} // namespace ForEach


namespace AllAny {

using Adaptors::ToStl::toStl;

template<class Fn>
class Not 
{
  Fn _inner;
public:
  Not(Fn inner) : _inner(std::move(inner)) {}

  Fn operator!() { return std::move(_inner); }

  template<class Arg>
  bool operator()(Arg iter) 
  { return !_inner(iter); }
};

template<class F>
class Any { 
  F _f;
public:
  Any(F f) : _f(f) {}

  Not<Any> operator!() 
  { return Not<Any>(std::move(*this)); }

  template<class Iter>
  bool operator()(Iter iter) 
  { 
    for ( ElemT<Iter> x : iter | toStl()) {
      if (_f(x))
        return true;
    }
    return false;
  }
};

template<class F>
Any<F> any(F f)
{ return Any<F>(f); }

template<class F> 
using All = Not<Any<Not<F>>>;

template<class F>
All<F> all(F f)
{ return !any(Not<F>(f)); }

} // namespace AllAny

namespace Fold {
using Adaptors::ToStl::toStl;

template<class A, class F>
class Fold {
  A _state;
  F _combine;
public:
  Fold(A initial, F combine): _state(std::move(initial)), _combine(std::move(combine)) {}
  
  template<class Iter>
  typename std::result_of<F(A, ElemT<Iter>)>::type operator()(Iter i) 
  {
    typename std::result_of<F(A, ElemT<Iter>)>::type state = std::move(_state);
    for ( ElemT<Iter> x : i | toStl()) {
      state = _combine(std::move(state), std::forward<ElemT<Iter>>(x));
    }
    return state;
  }
};

template<class A, class F>
Fold<A,F> fold(A initial, F combine)
{ return Fold<A,F>(std::move(initial), std::move(combine)); }


template<class F>
class FoldNonEmpty {
  F _combine;
public:
  FoldNonEmpty(F combine): _combine(std::move(combine)) {}
  
  template<class Iter>
  using ResultT = typename std::result_of<F(ElemT<Iter>&&, ElemT<Iter>&&)>::type;

  template<class Iter>
  Option<ResultT<Iter>> operator()(Iter i) 
  {
    if (i.hasNext()) {
      ResultT<Iter> state = std::move(i.next());
      for (ElemT<Iter> x : i | toStl()) {
        state = _combine(std::move(state), std::forward<ElemT<Iter>>(x));
      }
      return Option<ResultT<Iter>>(std::move(state));
    } else {
      return Option<ResultT<Iter>>();
    }
  }
};

template<class F>
FoldNonEmpty<F> fold(F combine)
{ return FoldNonEmpty<F>(std::move(combine)); }


} // namespace Fold

} // namespace Destructors

///////////////////////////////////////////////////////////////////////////////////////
// RE-EXPORTS
//////////////////////

using Adaptors::Map::map;
using Adaptors::Filter::filter;
using Adaptors::ToStl::toStl;
using Adaptors::Flatten::flatten;
using Adaptors::FlatMap::flatMap;
using Adaptors::Cloned::cloned;
using Adaptors::SizeHint::sizeHint;

using Destructors::Collect::collect;
using Destructors::ForEach::forEach;
using Destructors::AllAny::all;
using Destructors::AllAny::any;
using Destructors::Fold::fold;

} // namespace Iteartor
} // namespace Lib


#endif // __LIB__ITERATOR__HPP__
