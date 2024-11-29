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
 * @file Forwards.hpp
 * Forward declarations of some classes
 */
#ifndef __Debug_Output_HPP__
#define __Debug_Output_HPP__

#include <iostream>
#include <utility>
#include <tuple>

namespace std {
template<class... As> 
std::ostream& operator<<(std::ostream& out, tuple<As...> const& self);
} // namespace std

namespace Kernel {

/** Newtype in order to nicely output a pointer.
 * Usage: `out << outputPtr(ptr) << std::endl;` 
 */
template<class T>
struct OutputMaybePtr { T const& self; };

template<class T>
OutputMaybePtr<T> outputMaybePtr(T const& self) { return { .self = self, }; }

/** Newtype in order to nicely output a pointer.
 * Usage: `out << outputPtr(ptr) << std::endl;` 
 */
template<class T>
struct OutputPtr { T* self; };

template<class T>
OutputPtr<T> outputPtr(T* self) { return { .self = self, }; }

template<class T>
struct RepeatOutput { T const& to_repeat; unsigned times; };

template<class T>
RepeatOutput<T> repeatOutput(T const& c, unsigned times)
{ return RepeatOutput<T>{c, times}; }

/** Newtype for outputting a datatype that implements it in multiline format.
 * Usage: `out << multiline(substitutioTree) << std::endl;` 
 *
 * You can implement this for a `MyType` by implementing 
 * std::ostream& operator<<(std::ostream&, OutputMultiline<MyType>)
 */
template<class T>
struct OutputMultiline { 
  T const& self; 
  unsigned indent; 

  static void outputIndent(std::ostream& out, unsigned indent);
};

template<class T>
OutputMultiline<T> multiline(T const& self, unsigned indent = 0)
{ return { self, indent, }; }

template<class Sep, class Iter>
struct OutputInterleaved { Sep const& sep; Iter iter; };

template<class Sep, class Iter>
struct OutputInterleaved<Sep,Iter> outputInterleaved(Sep const& s, Iter i)
{ return OutputInterleaved<Sep, Iter>{s, std::move(i)}; }

template<class Iter>
auto commaSep(Iter i) { return outputInterleaved(", ", std::move(i)); }


template<class... Elems>
struct OutputCat { std::tuple<Elems...> elems; };

template<class... Elems>
struct OutputCat<Elems...> outputCatOwned(Elems... elems)
{ return OutputCat<Elems...>{std::make_tuple(elems...)}; }

template<class... Elems>
struct OutputCat<Elems const&...> outputCat(Elems const&... elems)
{ return OutputCat<Elems const&...>{std::tie(elems...)}; }

struct OutputNothing {
  friend std::ostream& operator<<(std::ostream& out, OutputNothing const& self)
  { return out << ""; }
};

struct OutputComma {
  friend std::ostream& operator<<(std::ostream& out, OutputComma const& self)
  { return out << ", "; }
};

template<unsigned i, unsigned sz, class Tup, class Sep> 
struct __OutputTuple
{
  static void apply(std::ostream& out, Tup const& self)
  {
   out << Sep{} << std::get<i>(self);
    __OutputTuple<i + 1, sz, Tup, Sep>::apply(out, self);
  }
};

template<class Sep> 
struct __OutputTuple<0, 0, std::tuple<>, Sep>  
{ static void apply(std::ostream& out, std::tuple<> const& self) { } };

template<unsigned sz, class Tup, class Sep> 
struct __OutputTuple<sz, sz, Tup, Sep>  
{ static void apply(std::ostream& out, Tup const& self) { } };


template<unsigned sz, class Tup, class Sep> 
struct __OutputTuple<0, sz, Tup, Sep>  
{
  static void apply(std::ostream& out, Tup const& self)
  {
    out << std::get<0>(self);
    __OutputTuple<1, sz, Tup, Sep>::apply(out, self);
  }
};


template<class Sep, class Iter>
std::ostream& operator<<(std::ostream& out, Kernel::OutputInterleaved<Sep, Iter> self)
{
  if (self.iter.hasNext()) {
    out << self.iter.next();
    while (self.iter.hasNext()) {
      out << self.sep << self.iter.next();
    }
  }
  return out;
}

template<class... As> 
std::ostream& operator<<(std::ostream& out, OutputCat<As...> const& self)
{ 
  Kernel::__OutputTuple<0, std::tuple_size<std::tuple<As...>>::value, std::tuple<As...>, OutputNothing>::apply(out, self.elems);
  return out;
}



template<class T>
std::ostream& operator<<(std::ostream& out, Kernel::RepeatOutput<T> const& self)
{ for (unsigned i = 0; i < self.times; i++) out << self.to_repeat; return out; };

template<class T>
std::ostream& operator<<(std::ostream& out, Kernel::OutputPtr<T> const& self)
{ return self.self ? out << *self.self : out << "NULL"; }

template<class T>
std::ostream& operator<<(std::ostream& out, Kernel::OutputMaybePtr<T*> const& self)
{ return self.self ? out << *self.self : out << "NULL"; }

template<class T>
std::ostream& operator<<(std::ostream& out, Kernel::OutputMaybePtr<T> const& self)
{ return out << self.self; }

template<class T>
void Kernel::OutputMultiline<T>::outputIndent(std::ostream& out, unsigned indent)
{ out << repeatOutput("    ", indent); };



} // namespace Kernel

namespace std {

template<class A, class B>
std::ostream& operator<<(std::ostream& out, pair<A,B> const& self)
{ return out << "(" << self.first << ", " << self.second << ")"; }


template<class... As> 
std::ostream& operator<<(std::ostream& out, tuple<As...> const& self)
{ 
  out << "(";
  Kernel::__OutputTuple<0, std::tuple_size<std::tuple<As...>>::value, std::tuple<As...>, Kernel::OutputComma>::apply(out, self);
  out << ")";
  return out;
}

} // namespace std

// namespace Kernel { using ::operator<<; }

#endif // __Debug_Output_HPP__
