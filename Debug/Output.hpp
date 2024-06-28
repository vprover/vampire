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

template<class... As> 
std::ostream& operator<<(std::ostream& out, std::tuple<As...> const& self);

namespace Kernel {


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

// } // namespace Kernel
//
// namespace Kernel {


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

template<unsigned i, unsigned sz, class Tup> 
struct __OutputTuple
{
  static void apply(std::ostream& out, Tup const& self)
  {
   out << ", " << std::get<i>(self);
    __OutputTuple<i + 1, sz, Tup>::apply(out, self);
  }
};

template<> 
struct __OutputTuple<0, 0, std::tuple<>>  
{ static void apply(std::ostream& out, std::tuple<> const& self) { } };

template<unsigned sz, class Tup> 
struct __OutputTuple<sz, sz, Tup>  
{ static void apply(std::ostream& out, Tup const& self) { } };


template<unsigned sz, class Tup> 
struct __OutputTuple<0, sz, Tup>  
{
  static void apply(std::ostream& out, Tup const& self)
  {
    out << std::get<0>(self);
    __OutputTuple<1, sz, Tup>::apply(out, self);
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
template<class T>
std::ostream& operator<<(std::ostream& out, Kernel::RepeatOutput<T> const& self)
{ for (int i = 0; i < self.times; i++) out << self.to_repeat; return out; };

template<class T>
std::ostream& operator<<(std::ostream& out, Kernel::OutputPtr<T> const& self)
{ return self.self ? out << *self.self : out << "NULL"; }
template<class T>
void Kernel::OutputMultiline<T>::outputIndent(std::ostream& out, unsigned indent)
{ out << repeatOutput("    ", indent); };

} // namespace Kernel


template<class A, class B>
std::ostream& operator<<(std::ostream& out, std::pair<A,B> const& self)
{ return out << "(" << self.first << ", " << self.second << ")"; }


template<class... As> 
std::ostream& operator<<(std::ostream& out, std::tuple<As...> const& self)
{ 
  out << "(";
  Kernel::__OutputTuple<0, std::tuple_size<std::tuple<As...>>::value, std::tuple<As...>>::apply(out, self);
  out << ")";
  return out;
}


#endif // __Debug_Output_HPP__
