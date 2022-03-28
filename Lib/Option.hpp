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
 * This file mainly defined the class Option, which can be thought of as a NULLable pointer, that is 
 * stack-allocated, with RAII semantics. 
 *
 * \see UnitTests/tOption.cpp for examples of the usage
 */
#ifndef __OPTIONAL_H__
#define __OPTIONAL_H__

#include <type_traits>
#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include <iostream>


namespace Lib {


#define FOR_REF_QUALIFIER(macro)                                                                              \
  macro(const &, ) macro(&, ) macro(&&, std::move)

template<class T>
struct MaybeUninit {
  union Value { 
    T init; int uninint[0]; 
    Value() : uninint{} {};
    ~Value() {};
  } _elem;

   MaybeUninit() : _elem() {}
  ~MaybeUninit() {}
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MV)                                                                            \
  operator T REF() REF                                                                                        \
  { return MV(_elem.init); }                                                                                  \
                                                                                                              \
  void init(T REF content)                                                                                    \
  { ::new(&_elem.init)T(MV(content)); }                                                                       \
                                                                                                              \
  MaybeUninit& operator=(T REF content)                                                                       \
  {                                                                                                           \
    _elem.init = MV(content);                                                                                 \
    return *this;                                                                                             \
  }                                                                                                           \

  FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier 
};

template<class A>
class OptionBase 
{

  bool _isSome;
  MaybeUninit<A> _elem;
public:

  OptionBase() : _isSome(false) {}

  ~OptionBase() 
  { 
    CALL("~OptionBase") 
    if (isSome()) { 
      unwrap().~A(); 
    }
  }
  explicit OptionBase(A content)
    : _isSome(true)
      , _elem()
  {
    CALL("Option(A)")
    _elem.init(std::move(content));
  }
 
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MV)                                                                            \
                                                                                                              \
  A REF unwrap() REF                                                                                          \
  {                                                                                                           \
    ASS(_isSome);                                                                                             \
    return MV(_elem);                                                                                         \
  }                                                                                                           \
                                                                                                              \
  OptionBase(OptionBase REF a) : _isSome(a._isSome)                                                           \
  {                                                                                                           \
    CALL("OptionBase(OptionBase " #REF ")");                                                                  \
    if (isSome()) {                                                                                           \
      _elem.init(MV(a).unwrap());                                                                             \
    }                                                                                                         \
  }                                                                                                           \
                                                                                                              \
  OptionBase& operator=(OptionBase REF other)                                                                 \
  {                                                                                                           \
    CALL("OptionBase& operator=(OptionBase "#REF")");                                                         \
                                                                                                              \
    if (_isSome) {                                                                                            \
      if (other._isSome) {                                                                                    \
        unwrap() = MV(other).unwrap();                                                                        \
      } else {                                                                                                \
        unwrap().~A();                                                                                        \
      }                                                                                                       \
    } else {                                                                                                  \
      ASS(isNone())                                                                                           \
      if (other._isSome){                                                                                     \
         _elem.init(MV(other).unwrap());                                                                      \
      } else {                                                                                                \
         /* nothing to do */                                                                                  \
      }                                                                                                       \
    }                                                                                                         \
    _isSome = other._isSome;                                                                                  \
    return *this;                                                                                             \
  }                                                                                                           \

  FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier

  bool isSome() const { return _isSome;   }
  bool isNone() const { return !isSome(); }

  static OptionBase fromPtr(A* ptr) 
  { return ptr == nullptr ? OptionBase() : OptionBase(*ptr); }

  friend bool operator==(OptionBase const& lhs, OptionBase const& rhs) 
  { 
    if (lhs._isSome != rhs._isSome) return false;
    
    if (lhs._isSome) {
      return lhs.unwrap() == rhs.unwrap();
    } else {
      return true;
    }
  }
    
};



template<class A>
class OptionBaseRef
{
  A* _elem;
public:

  OptionBaseRef(          ) : _elem(nullptr) {  }
  OptionBaseRef(A const* content) : _elem(const_cast<A*>(content)) { }
  OptionBaseRef(A* content) : _elem(content) { }

  bool isSome() const { return _elem != nullptr;   }

  A const& unwrap() const& { ASS(isSome()); return           *_elem ; }
  A     && unwrap()     && { ASS(isSome()); return std::move(*_elem); }
  A      & unwrap()      & { ASS(isSome()); return           *_elem ; }

  OptionBaseRef(OptionBaseRef      & a) = default;
  OptionBaseRef(OptionBaseRef     && a) = default;
  OptionBaseRef(OptionBaseRef const& a) = default;

  OptionBaseRef& operator=(OptionBaseRef      & a) = default;
  OptionBaseRef& operator=(OptionBaseRef     && a) = default;
  OptionBaseRef& operator=(OptionBaseRef const& a) = default;

  static OptionBaseRef fromPtr(A* ptr) 
  { return ptr == nullptr ? OptionBaseRef() : *ptr; }

  friend bool operator==(OptionBaseRef const& lhs, OptionBaseRef const& rhs) 
  { return *lhs._elem == *rhs._elem; }

};

template<class A>
class OptionBase<A const&> : public OptionBaseRef<A>
{
public:
  OptionBase() : OptionBaseRef<A>() {}
  OptionBase(A const& item) : OptionBaseRef<A>(&item) {}
  OptionBase(OptionBase const& b) : OptionBaseRef<A>(b) {}
};

template<class A>
class OptionBase<A&> : public OptionBaseRef<A>
{
public:
  OptionBase() : OptionBaseRef<A>() {}
  OptionBase(A& item) : OptionBaseRef<A>(&item) {}
  OptionBase(OptionBase const& b) : OptionBaseRef<A>(b) {}
};

/** The actual Option class
 * An Option<A> is a class that holds either a value of type A, or is none/empty.
 * It can be thought of a nullable pointer, that has the advantage that does not need to be allocated 
 * in a separate structure, and does not expose any uninitialized memory to the user. Further it 
 * automatically calls the destructor when it goes out of scope.
 *
 * \see UnitTests/tOption.cpp for usage examples
 */
template<class A>
class Option : OptionBase<A> {

  explicit Option(OptionBase<A>&& base) : OptionBase<A>(std::move(base)) {  }
public:
  using Content = A;

  /** constructs an option from a value of type A&, A const&, or A&&. */
  using OptionBase<A>::OptionBase;

  /** checks whether the Option holds a value */
  using OptionBase<A>::isSome;

  /** returns the Options value if it holds one */
  using OptionBase<A>::unwrap;

  friend bool operator==(Option const& lhs, Option const& rhs) 
  { return static_cast<OptionBase<A>const&>(lhs) == static_cast<OptionBase<A>const&>(rhs); }

  friend bool operator!=(Option const& lhs, Option const& rhs) 
  { return !(lhs == rhs); }

  /** creates an Option<A&>, or Option<A const&> from a pointer A*. if the pointer is NULL the option will be empty */
  template<class C> static Option<A> fromPtr(C self) 
  { return Option(OptionBase<A>::fromPtr(self)); }

  /** checks whether the option is empty */
  bool isNone() const { return !this->isSome(); }

  /** 
   * returns the value held by this option if there is one, or calls the given function f without arguments, 
   * initializes the closuer with the returned value, and returns a reference to the value afterwards.
   */ 
  template<class Clsr>
  A& unwrapOrInit(Clsr f) { 
    if (isNone()) {
      ::new(this) Option(f());
    }
    return this->unwrap();
  }

// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
                                                                                                              \
  /**                                                                                                         \
   * applies the given function to the value of this option and returns an option of the return type.         \
   * if the Option was None an empty option of the function's return type is returned.                        \
   */                                                                                                         \
  template<class Clsr>                                                                                        \
  Option<typename std::result_of<Clsr(A REF)>::type> map(Clsr clsr) REF {                                     \
    using OptOut = Option<typename std::result_of<Clsr(A REF)>::type>;                                        \
    return this->isSome() ? OptOut(clsr(MOVE(this->unwrap())))                                                \
                          : OptOut();                                                                         \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * if the Option holds a value the first function is applied to the value.                                  \
   * if the Option is none the second function is called without arguments and the result is returned.        \
   * \pre both CaseSome and CaseNone must have the same return type                                           \
   */                                                                                                         \
  template<class CaseSome, class CaseNone>                                                                    \
  typename std::result_of<CaseSome( A REF)>::type match(CaseSome present, CaseNone none) REF {                \
    if (this->isSome()) {                                                                                     \
      return present(MOVE((*this)).unwrap());                                                                 \
    } else {                                                                                                  \
      return none();                                                                                          \
    }                                                                                                         \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * returns the value held by this option if there is one, or calls the given function f without arguments   \
   * and returns the value otherwise.                                                                         \
   */                                                                                                         \
  template<class Clsr>                                                                                        \
  A unwrapOrElse(Clsr f) REF {                                                                                \
    if (this->isSome()) {                                                                                     \
      return MOVE(*this).unwrap();                                                                            \
    } else {                                                                                                  \
      return f();                                                                                             \
    }                                                                                                         \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * applies a function to the value of this closure if ther is one. the function is expected to return       \
   * another option. the resulting Option<Option<Result>> will then be flattened to an Option<Result>.        \
   *                                                                                                          \
   * This function is the same as flatMap/andThen/(>>=)  in other programming languages with monads.          \
   */                                                                                                         \
  template<class Clsr>                                                                                        \
  typename std::result_of<Clsr(A REF)>::type andThen(Clsr clsr) REF {                                         \
    using OptOut = typename std::result_of<Clsr(A REF)>::type;                                                \
    return this->isSome() ? clsr(MOVE(*this).unwrap())                                                        \
                          : OptOut();                                                                         \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * turns an Option<A&>, Option<A const&>, or Option<A&&> into an Option<A> by calling the appropriate move  \
   * or copy constructor.                                                                                     \
   */                                                                                                         \
  Option<typename std::remove_const<typename std::remove_reference<A>::type>::type>  toOwned() REF            \
  {                                                                                                           \
    using Out = typename std::remove_const<typename std::remove_reference<A>::type>::type;                    \
    return map([](A REF  elem) -> Out { return Out(MOVE(elem)); });                                           \
  }                                                                                                           \

  FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier

  friend std::ostream& operator<<(std::ostream& out, Option const& self) 
  { return self.isSome() ?  out << self.unwrap() : out << "None"; }
};

template<class T> Option<T> some(T const& t) { return Option<T>(          t ); }
template<class T> Option<T> some(T      & t) { return Option<T>(          t ); }
template<class T> Option<T> some(T     && t) { return Option<T>(std::move(t)); }
template<class T> Option<T> none()    { return Option<T>(); }

template<class T>
Option<T> optionFromPtr(T* t) 
{ return Option<T>::fromPtr(t); }

}

#endif // __OPTIONAL_H__
