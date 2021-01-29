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
#include "Lib/TimeCounter.hpp"


namespace Lib {

  // TODO move to reflection
template<class T>
struct ElementTypeInfo<std::unique_ptr<T>> {
  using Type = ELEMENT_TYPE(T);
};

template<class T,
         typename std::enable_if<
            !std::is_lvalue_reference<T>::value
         && !std::is_rvalue_reference<T>::value
           , bool>::type = true
         >
typename std::remove_reference<T>::type&& moveValue( T& t ) noexcept
{ return std::move(t); }

template<class T,
         typename std::enable_if<std::is_rvalue_reference<T>::value, bool>::type = true
         >
typename std::remove_reference<T>::type&& moveValue( T&& t ) noexcept
{ return std::move(t); }

template<class T,
         typename std::enable_if<std::is_lvalue_reference<T>::value, bool>::type = true
         >
typename std::remove_reference<T>::type& moveValue( T&& t ) noexcept
{ return t; }


namespace Iterator {


template<class Iter>
using ElemT = ELEMENT_TYPE(Iter);

template<class Iter, class Enable = void>
struct is_iterator 
{ static constexpr bool value = false; };

template<class Iter>
struct is_iterator<Iter, typename std::enable_if<Iter::template __is_iterator<void>::value>::type>
{ static constexpr bool value = true; };

template<class Iter, class Enable = void>
struct is_legacy_iterator 
{
  static constexpr bool value = false;
};


template<class Iter>
struct is_legacy_iterator<Iter,
  typename std::enable_if<
             std::is_same<decltype(((Iter      *)nullptr)->    next()), ElemT<Iter>   >::value
           >::type
           >
{ 
  static constexpr bool value = true;
};

#define ASSERT_ITERATOR(...)                                                                                  \
  static_assert(is_iterator<__VA_ARGS__>::value, "not an iterator type")

template<class Iter, class Adaptor>
typename std::result_of<Adaptor(Iter)>::type operator|(Iter iter, Adaptor adaptor) 
{ 
  ASSERT_ITERATOR(Iter);
  return adaptor(std::move(iter)); 
}

/** This class is to be used in the context of a for (auto x : ...) loop only. */
template<class Iter>
class ForLoopIter 
{
  Option<Iter&> _iter; // <- nothing here encodes that this == end()
  Option<ElemT<Iter>>  _cur;

public:
  ForLoopIter(Iter& iter)  : _iter(Option<Iter&>(iter)), _cur(iter.next()) {}
  ForLoopIter()  : _iter(), _cur() {}

  void operator++() 
  { _cur = _iter.unwrap().next(); }

  ElemT<Iter> operator*() 
  { return moveValue<ElemT<Iter>>(_cur.unwrap()); } 

  friend bool operator!=(ForLoopIter const& lhs, ForLoopIter const& rhs) 
  { return !(lhs == rhs); }

  friend bool operator==(ForLoopIter const& lhs, ForLoopIter const& rhs) 
  { 
    ASS(rhs._iter.isNone()); 
    ASS(lhs._iter.isSome()); 
    return lhs._cur.isNone(); 
  }
};

#define ASSERT_METHOD(Return, Class, method, constness)                                                       \
    static_assert(std::is_same<decltype(((Class constness*)nullptr)->method), Return>::value,                 \
                  "method not implemented: " #Return " " #Class "::" #method " " #constness );                \

#define DERIVE_ITERATOR(Class)                                                                                \
  auto begin() -> ForLoopIter<Class> { return ForLoopIter<Class>(*this);  }                                   \
  auto end()   -> ForLoopIter<Class> { return ForLoopIter<Class>();       }                                   \
  template<class Dummy> struct __is_iterator                                                                  \
  {                                                                                                           \
    ASSERT_METHOD(Option<unsigned>, Class, sizeLeft(), const);                                                \
    ASSERT_METHOD(Option<ElemT<Class>>, Class, next(), );                                                     \
    static constexpr bool value = true;                                                                       \
  };                                                                                                          \



///////////////////////////////////////////////////////////////////////////////////////
// BASE ITERATORS
//////////////////////

namespace Iterators {

template<class E>
class DynIter 
{
  template<class El> class Interface 
  {
  public:
    DECL_ELEMENT_TYPE(El);
    virtual Option<E> next() = 0;
    virtual Option<unsigned> sizeLeft() const = 0;
    virtual ~Interface() {}
  };

  template<class Iter> class Implementation : public Interface<ElemT<Iter>>
  {
    Iter _iter;
  public:
    Implementation(Iter iter) : _iter(std::move(iter)) { }
    virtual Option<ElemT<Iter>> next()        override { return _iter.next(); }
    virtual Option<unsigned> sizeLeft() const override { return _iter.sizeLeft(); }
    virtual ~Implementation() {}
  };


  std::unique_ptr<Interface<E>> _iter;
public:
  DECL_ELEMENT_TYPE(E);
  DERIVE_ITERATOR(DynIter)

  template<class Iter>
  DynIter(Iter iter) : _iter(new Implementation<Iter>(std::move(iter))) { }

  inline Option<E> next()                  { return _iter->next(); }
  inline Option<unsigned> sizeLeft() const { return _iter->sizeLeft(); }
};

template<class Iter>
DynIter<ElemT<Iter>> dyn(Iter iter) 
{ return DynIter<ElemT<Iter>>(std::move(iter)); }

/** Iterator for any object that implements the indexing operator */
template<class Array, class Idx = unsigned>
class IndexIter 
{
  Array _array;
  Idx _idx;
  Idx _size;
public:
  DECL_ELEMENT_TYPE(decltype(_array[_idx]));
  DERIVE_ITERATOR(IndexIter)

  IndexIter(Array array, Idx size) : _array(std::move(array)), _idx(0), _size(_array.size()) {}
  IndexIter(Array array) : IndexIter(std::move(array), array.size()) {}

  Option<ElemT<IndexIter>> next() 
  { return _idx < _size ? Option<ElemT<IndexIter>>(_array[_idx++]) 
                        : Option<ElemT<IndexIter>>(); }

  Option<unsigned> sizeLeft() const 
  { return Option<unsigned>(_size - _idx); }
};

template<class Array>
class ArrayRef {
  Array* _self;
public:
  ArrayRef(Array* self) : _self(self) {}
  template<class Idx> auto operator[](Idx i) -> decltype((*_self)[i])   { return (*_self)[i];  }
                      auto size()            -> decltype(_self->size()) { return _self->size(); }
};

template<class Array>
auto indexIter(Array&& array) -> IndexIter<Array, decltype(array.size())>
{ return IndexIter<Array, decltype(array.size())>(std::move(array)); }

template<class Array, class Idx>
auto indexIter(Array&& array, Idx size) -> IndexIter<Array, Idx>
{ return IndexIter<Array, Idx>(std::move(array), size); }

template<class Array>
auto indexIter(Array& array) -> IndexIter<ArrayRef<Array>, decltype(array.size())>
{ return IndexIter<ArrayRef<Array>, decltype(array.size())>(ArrayRef<Array>(&array)); }

template<class Array, class Idx>
auto indexIter(Array& array, Idx size) -> IndexIter<ArrayRef<Array>, Idx>
{ return IndexIter<ArrayRef<Array>, Idx>(ArrayRef<Array>(&array), size); }


template<class Number>
class RangeIter {
  Number _idx;
  Number const _endExclusive;
public:
  DECL_ELEMENT_TYPE(Number);
  DERIVE_ITERATOR(RangeIter)
  RangeIter(Number start, Number endExclusive) : _idx(start), _endExclusive(endExclusive) {}

  Option<Number> next() 
  { return  _idx < _endExclusive ? Option<Number>(_idx++) 
                                 : Option<Number>(); }

  Option<unsigned> sizeLeft() const 
  { return Option<unsigned>(_endExclusive - _idx); }
};

template<class Number> auto rangeExcl(Number start, Number end) -> RangeIter<Number>
{ return RangeIter<Number>(start, end); }

template<class Number> auto rangeIncl(Number start, Number end) -> RangeIter<Number>
{ return RangeIter<Number>(start, end + 1); }

// TODO remove me
template<class Iter>
class IterWrapper {
  Iter _iter;
public:
  DECL_ELEMENT_TYPE(ELEMENT_TYPE(Iter));
  DERIVE_ITERATOR(IterWrapper)
  IterWrapper(Iter iter) : _iter(std::move(iter)) {}

  Option<ElemT<Iter>> next() 
  { return _iter.hasNext() ? Option<ElemT<Iter>>(_iter.next()) 
                           : Option<ElemT<Iter>>(); }

  Option<unsigned> sizeLeft() const 
  { return _iter.knownSize() ? Option<unsigned>(_iter.size())
                             : Option<unsigned>(); }

};

template<class Iter>
IterWrapper<Iter> wrap(Iter iter) 
{ return IterWrapper<Iter>(std::move(iter)); }

} // namespace Iterators

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

template<class Iter, class Func, class Enable = void>
class Map 
{
  Iter _iter;
  Func _func;
public:
  using Result = typename std::result_of<Func(ElemT<Iter>)>::type;
  DECL_ELEMENT_TYPE(Result);
  DERIVE_ITERATOR(Map)

  Map(Iter inner, Func func) : _iter(std::move(inner)), _func(std::move(func)) {}

  inline Option<Result> next() 
  { 
    auto res = _iter.next();
    if (res.isSome()) {
      return Option<Result>(_func(moveValue<ElemT<Iter>>(res.unwrap())));
    } else {
      return Option<Result>();
    }
  }

  inline Option<unsigned> sizeLeft() const { return _iter.sizeLeft(); }
};


template<class Iter, class Func>
class Map<Iter, Func, 
      typename std::enable_if< 
                    is_legacy_iterator<
                         typename std::result_of<Func(ElemT<Iter>)>::type 
                    >::value
               >::type>
{
  Iter _iter;
  Func _func;
public:
  using Result = Iterators::IterWrapper<typename std::result_of<Func(ElemT<Iter>)>::type>;

  DECL_ELEMENT_TYPE(Result);
  DERIVE_ITERATOR(Map)

  Map(Iter inner, Func func) : _iter(std::move(inner)), _func(std::move(func)) {}

  inline Option<Result> next()           
  { Option<typename std::result_of<Func(ElemT<Iter>)>::type> out = _iter.next().map(_func); 
    if (out.isSome()) {
      return Option<Result>(Iterators::wrap(std::move(out).unwrap()));
    } else {
      return Option<Result>();
    }
  }

  inline Option<unsigned> sizeLeft() const { return _iter.sizeLeft(); }
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
public:
  DECL_ELEMENT_TYPE(ElemT<Iter>);
  DERIVE_ITERATOR(Filter)

  Filter(Iter inn, Func func)
  : _func(func), _inn(inn) {}

  Option<ElemT<Iter>> next() 
  {
    CALL("Filter::next")
    for (auto e = _inn.next(); e.isSome(); e = _inn.next()) {
      if (_func(e.unwrap())) 
        return e;
    }
    return Option<ElemT<Iter>>();
  }

  inline Option<unsigned> sizeLeft() const { return Option<unsigned>(); }
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
  Outer _outer;
  Option<Inner> _current;
  bool _init;
public:
  ASSERT_ITERATOR(Outer);
  ASSERT_ITERATOR(ElemT<Outer>);
  DECL_ELEMENT_TYPE(ElemT<Inner>);
  DERIVE_ITERATOR(Flatten)

  explicit Flatten(Outer master)
  : _outer(std::move(master))
  , _current()
  , _init(false)
  { }

  Option<ElemT<Inner>> next()
  {
    CALL("Flatten::next");
    if (!_init) {
      _init = true;
      _current = _outer.next();
    }
    using Out = Option<ElemT<Flatten>>;
    if (_current.isNone()) {
      return Out();
    }
    Out e = _current.unwrap().next();
    if (e.isSome()) {
      return e;
    } else {
      while (e.isNone()) {
        _current = _outer.next();
        if (_current.isNone())
          break;
        e = _current.unwrap().next();
      }
      return e;
    }
  }

  inline Option<unsigned> sizeLeft() const 
  { return Option<unsigned>(); }
};

inline Adaptor<Flatten> flatten() 
{ return Adaptor<Flatten>(); }

} // namespace Flatten

namespace Cloned {

using Map::Map;

struct Clone {
  template<class A> A operator()(A const& val) { return A(val); }
  template<class A> A operator()(A      & val) { return A(val); }
  template<class A> A operator()(A     && val) { return A(val); }
};

inline Adaptor<Map, Clone> cloned() 
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
  DERIVE_ITERATOR(SizeHint)


  SizeHint(Iter iter, Unsigned size) : _iter(std::move(iter)) , _size(size) { }

  Option<ElemT<Iter>> next()
  { 
    ASS_GE(_size, 0)
    _size--; 
    return _iter.next(); 
  }

  inline Option<unsigned> sizeLeft() const
  { return Option<unsigned>(_size); }
};

inline Adaptor<SizeHint, unsigned> sizeHint(unsigned size) 
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
  DERIVE_ITERATOR(FlatMap)

  FlatMap(Iter i, F f) 
    : _self(Self(SelfMap(std::move(i), std::move(f)))) {}

  Option<ElemT<Self>> next()               { return _self.next(); }
  inline Option<unsigned> sizeLeft() const { return _self.sizeLeft(); }

};

template<class F>
Adaptor<FlatMap, F> flatMap(F f) 
{ return Adaptor<FlatMap, F>(std::move(f)); }


} // namespace FlatMap

namespace TimeCounted {

template<class Inner, class TCU>
class TimeCounted
{
public:
  DECL_ELEMENT_TYPE(ElemT<Inner>);
  DERIVE_ITERATOR(TimeCounted)

  TimeCounted(Inner inn, TimeCounterUnit tcu)
  : _inn(std::move(inn)), _tcu(tcu) {}

  inline Option<ElemT<Inner>> next()
  {
    TimeCounter tc(_tcu);
    return _inn.next();
  };


  inline Option<unsigned> sizeLeft() const
  { return _inn.sizeLeft(); };

private:
  Inner _inn;
  TimeCounterUnit _tcu;
};


inline Adaptor<TimeCounted, TimeCounterUnit> timeCounted(TimeCounterUnit tcu) 
{ return Adaptor<TimeCounted, TimeCounterUnit>(tcu); }

} // namespace TimeCounted

} // namespace Adaptors

///////////////////////////////////////////////////////////////////////////////////////
// ITERATOR COMBINATORS
//////////////////////

namespace Combinators {

namespace Concat {

template<class Iter1, class Iter2>
class Concat {
  enum { Fst, Snd, End } _idx;
  Iter1 _i1;
  Iter2 _i2;
public:
  static_assert(std::is_same<ElemT<Iter1>, ElemT<Iter2>>::value, 
      "can only concat iterators with same element types");
  DECL_ELEMENT_TYPE(ElemT<Iter1>);
  DERIVE_ITERATOR(Concat)

  Concat(Iter1 i1, Iter2 i2) : _idx(Fst), _i1(std::move(i1)), _i2(std::move(i2)) {}

  Option<ElemT<Concat>> next() 
  {
    switch (_idx) {
      case Fst: {
        Option<ElemT<Concat>> e = _i1.next();
        if (e.isSome()) {
          return e;
        } else {
          _idx = Snd;
          return next();
        }
      }
      case Snd: {
        Option<ElemT<Concat>> e = _i2.next();
        if (e.isSome()) {
          return e;
        } else {
          _idx = End;
          return next();
        }
      }
      case End:
        return Option<ElemT<Concat>>();
    }
    ASSERTION_VIOLATION
  }

  Option<unsigned> sizeLeft() const 
  {
    return _i1.sizeLeft().andThen([&](unsigned i){ 
      return _i2.sizeLeft().map([&](unsigned j){ 
          return i + j; 
      });  
    });
  }

};

template<class Iter1, class Iter2>
Concat<Iter1, Iter2> concat(Iter1 i1, Iter2 i2) 
{ return Concat<Iter1, Iter2>(std::move(i1),std::move(i2)); }

template<class Iter1, class Iter2, class Iter3, class... Iters>
auto concat(Iter1 i1, Iter2 i2, Iter3 i3, Iters... is) -> decltype(concat(Concat<Iter1, Iter2>(std::move(i1),std::move(i2)), std::move(i3), std::move(is)...))
{ return concat(Concat<Iter1, Iter2>(std::move(i1),std::move(i2)), std::move(i3), std::move(is)...); }

} // namespace Concat

} // namespace Combinators

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
  { return Container::fromIterator(std::move(iter)); }
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
  { return Container<ElemT<Iter>>::fromIterator(std::move(iter)); }
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
    for (ElemT<Iter> e : iter) {
      _f(moveValue<ElemT<Iter>>(e));
    }
  }
};

template<class F>
ForEach<F> foreach(F f)
{ return ForEach<F>(f); }

} // namespace ForEach


namespace AllAny {

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
    for ( ElemT<Iter> x : iter ) {
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
    for ( ElemT<Iter> x : i ) {
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
  using ResultT = typename std::result_of<F(typename std::remove_reference<ElemT<Iter>>::type&&, ElemT<Iter>)>::type;

  template<class Iter>
  Option<ResultT<Iter>> operator()(Iter i) 
  {
    Option<ElemT<Iter>> e = i.next();
    if (e.isSome()) {
      ResultT<Iter> state = std::move(e).unwrap();
      for (ElemT<Iter> x : i) {
        state = _combine(std::move(state), moveValue<ElemT<Iter>>(x));
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

namespace ToLegacy {

  template<class Iter>
  class Legacy {
    Iter _inner;
    Option<ElemT<Iter>> _current;
  public:
    DECL_ELEMENT_TYPE(ElemT<Iter>);
    Legacy(Iter inner) : _inner(std::move(inner)), _current() {}
    bool hasNext()     { return _current.isSome(); }
    ElemT<Iter> next() 
    { 
      ElemT<Iter> out = _current.unwrap();
      _current = _inner.next();
      return out;
    }
  };

  template<class Iter>
  Legacy<Iter> legacy(Iter iter) 
  { return Legacy<Iter>(std::move(iter)); }

} // namespace ToLegacy

} // namespace Destructors

///////////////////////////////////////////////////////////////////////////////////////
// RE-EXPORTS
//////////////////////

using Adaptors::Map::map;
using Adaptors::Filter::filter;
using Adaptors::Flatten::flatten;
using Adaptors::FlatMap::flatMap;
using Adaptors::Cloned::cloned;
using Adaptors::SizeHint::sizeHint;
using Adaptors::TimeCounted::timeCounted;

using Iterators::wrap;
using Iterators::rangeExcl;
using Iterators::rangeIncl;
using Iterators::indexIter;
using Iterators::dyn;
using Iterators::DynIter;

using Combinators::Concat::concat;

using Destructors::Collect::collect;
using Destructors::ForEach::foreach;
using Destructors::AllAny::all;
using Destructors::AllAny::any;
using Destructors::Fold::fold;
using Destructors::ToLegacy::legacy;

} // namespace Iteartor
} // namespace Lib

#endif // __LIB__ITERATOR__HPP__
