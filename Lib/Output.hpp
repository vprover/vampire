/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef __Lib_Output_HPP__
#define __Lib_Output_HPP__

#include <iosfwd>
#include <utility>
#include <concepts>
#include <tuple>
#include <string>
#include <sstream>
#include <type_traits>

namespace std {
template<class... As> 
std::ostream& operator<<(std::ostream& out, tuple<As...> const& self);
} // namespace std

namespace Lib {
namespace Output {

/** Anything that can be written with `out << value`. */
template<class T>
concept Printable = requires(std::ostream& out, T const& value) {
  { out << value } -> std::convertible_to<std::ostream&>;
};

/** Defer writing until insertion supplies the destination stream.
 * The callable is stored by value; any references it captures must remain valid.
 * Usage: out << deferred([](std::ostream& out) -> std::ostream& { return out << "text"; });
 */
template<class Write>
struct Deferred {
  Write write;

  friend std::ostream& operator<<(std::ostream& out, Deferred const& self)
  { return self.write(out); }
};

template<class Write>
Deferred<Write> deferred(Write write)
{ return {std::move(write)}; }

/** A member function that writes stored arguments to a stream. */
template<auto Write, class Object, class... Args>
concept MemberWriter = requires(Object* object, std::ostream& out, Args const&... args) {
  { (object->*Write)(out, args...) } -> std::convertible_to<std::ostream&>;
};

/** Bind a stream-writing member function, owning copies of its arguments.
 * The object itself must remain alive until the result is inserted.
 */
template<auto Write, class Object, class... Args>
  requires MemberWriter<Write, Object, std::decay_t<Args>...>
auto deferredMember(Object* object, Args&&... args)
{
  return deferred([object, args = std::make_tuple(std::forward<Args>(args)...)]
      (std::ostream& out) -> std::ostream& {
    return std::apply([&](auto const&... values) -> std::ostream& {
      return (object->*Write)(out, values...);
    }, args);
  });
}

/** Newtype in order to nicely output a pointer.
 * Usage: `out << Output::ptr(ptr) << std::endl;` 
 */
template<class T>
struct Ptr { T self; };

template<class T, std::enable_if_t<!std::is_pointer_v<T>, bool> = true>
Ptr<T const&> ptr(T const& self) { return { .self = self, }; }

template<class T, std::enable_if_t<std::is_pointer_v<T>, bool> = true>
Ptr<T> ptr(T self) { return { .self = self, }; }

template<class T>
std::ostream& operator<<(std::ostream& out, Ptr<T*> const& self)
{ return self.self == nullptr ? out << "NULL" : out << *self.self; }

template<class T>
std::ostream& operator<<(std::ostream& out, Ptr<T> const& self)
{ return out << self.self; }

template<class T>
struct Repeat { T const& to_repeat; unsigned times; };

template<class T>
Repeat<T> repeat(T const& c, unsigned times)
{ return Repeat<T>{c, times}; }

template<class T>
std::ostream& operator<<(std::ostream& out, Repeat<T> const& self)
{ for (unsigned i = 0; i < self.times; i++) out << self.to_repeat; return out; };

/** Newtype for outputting a datatype that implements it in multiline format.
 * Usage: `out << multiline(substitutioTree) << std::endl;` 
 *
 * You can implement this for a `MyType` by implementing 
 * std::ostream& operator<<(std::ostream&, Output::Multiline<MyType>)
 */
template<class T>
struct Multiline { 
  T const& self; 
  unsigned indent; 

  static void outputIndent(std::ostream& out, unsigned indent);
};

template<class T>
Multiline<T> multiline(T const& self, unsigned indent = 0)
{ return { self, indent, }; }

template<class T>
void Multiline<T>::outputIndent(std::ostream& out, unsigned indent)
{ out << Output::repeat("    ", indent); };



template<class Sep, class Iter>
struct Interleaved { Sep sep; Iter iter; };

template<class Sep, class Iter>
Interleaved<std::decay_t<Sep>, Iter> interleaved(Sep&& s, Iter i)
{ return {std::forward<Sep>(s), std::move(i)}; }

template<class Sep, class Iter>
std::ostream& operator<<(std::ostream& out, Interleaved<Sep, Iter> self)
{
  if (self.iter.hasNext()) {
    out << self.iter.next();
    while (self.iter.hasNext()) {
      out << self.sep << self.iter.next();
    }
  }
  return out;
}


template<class Iter>
auto commaSep(Iter i) { return Output::interleaved(", ", std::move(i)); }

struct Nothing {
  friend std::ostream& operator<<(std::ostream& out, Nothing const& self)
  { return out << ""; }
};

struct Comma {
  friend std::ostream& operator<<(std::ostream& out, Comma const& self)
  { return out << ", "; }
};


template<unsigned i, unsigned sz, class Tup, class Sep> 
struct __TupleHelper
{
  static void apply(std::ostream& out, Tup const& self)
  {
   out << Sep{} << std::get<i>(self);
    __TupleHelper<i + 1, sz, Tup, Sep>::apply(out, self);
  }
};

template<class Sep> 
struct __TupleHelper<0, 0, std::tuple<>, Sep>  
{ static void apply(std::ostream& out, std::tuple<> const& self) { } };

template<unsigned sz, class Tup, class Sep> 
struct __TupleHelper<sz, sz, Tup, Sep>  
{ static void apply(std::ostream& out, Tup const& self) { } };


template<unsigned sz, class Tup, class Sep> 
struct __TupleHelper<0, sz, Tup, Sep>  
{
  static void apply(std::ostream& out, Tup const& self)
  {
    out << std::get<0>(self);
    __TupleHelper<1, sz, Tup, Sep>::apply(out, self);
  }
};


template<class... Elems>
struct OutputCat { std::tuple<Elems...> elems; };

template<class... Elems>
struct OutputCat<Elems...> catOwned(Elems&&... elems)
{ return OutputCat<Elems...>{std::tuple<Elems...>(std::move(elems)...)}; }

template<class... Elems>
struct OutputCat<Elems const&...> cat(Elems const&... elems)
{ return OutputCat<Elems const&...>{std::tie(elems...)}; }

template<class... As> 
std::ostream& operator<<(std::ostream& out, OutputCat<As...> const& self)
{ 
  __TupleHelper<0, std::tuple_size<std::tuple<As...>>::value, std::tuple<As...>, Nothing>::apply(out, self.elems);
  return out;
}

// TODO deprecate
template<class... As>
std::string toString(As const&... as) {
  std::stringstream out;
  out << cat(as...);
  return out.str();
}
} // namespace Output
} // namespace Lib

namespace std {

template<class A, class B>
std::ostream& operator<<(std::ostream& out, pair<A,B> const& self)
{ return out << "(" << self.first << ", " << self.second << ")"; }


template<class... As> 
std::ostream& operator<<(std::ostream& out, tuple<As...> const& self)
{ 
  out << "(";
  Lib::Output::__TupleHelper<0, std::tuple_size<std::tuple<As...>>::value, std::tuple<As...>, Lib::Output::Comma>::apply(out, self);
  out << ")";
  return out;
}

} // namespace std

#endif // __Lib_Output_HPP__
