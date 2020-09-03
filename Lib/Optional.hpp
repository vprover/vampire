#ifndef __OPTIONAL_H__
#define __OPTIONAL_H__

#include <type_traits>
#include "Debug/Assertion.hpp"
#include <iostream>


namespace Lib {


#define FOR_REF_QUALIFIER(macro)                                                                              \
  macro(const &, ) macro(&, ) macro(&&, std::move)

template<class T>
struct MaybeUninit {
  typename std::aligned_storage<sizeof(T), alignof(T)>::type _elem;
  operator T const&()  const&{ return           *reinterpret_cast<T const*>(&_elem) ;}
  operator T      &()       &{ return           *reinterpret_cast<T      *>(&_elem) ;}
  operator T     &&()      &&{ return std::move(*reinterpret_cast<T      *>(&_elem));}

  void init(T     && content) { ::new(&_elem)T(std::move(content)); }
  void init(T      & content) { ::new(&_elem)T(          content ); }
  void init(T const& content) { ::new(&_elem)T(          content ); }
};

template<class A>
class OptionalBase 
{

  bool _isSome;
  MaybeUninit<A> _elem;
public:

  OptionalBase() : _isSome(false) {}
  OptionalBase(A     && content) : _isSome(true), _elem() { _elem.init(std::move(content)); }
  OptionalBase(A      & content) : _isSome(true), _elem() { _elem.init(          content ); }
  OptionalBase(A const& content) : _isSome(true), _elem() { _elem.init(          content ); }
  ~OptionalBase() { if (isSome()) { unwrap().~A(); } }

  bool isSome() const { return _isSome;   }
  bool isNone() const { return !isSome(); }

  A const& unwrap() const& { ASS(_isSome); return           _elem ; }
  A     && unwrap()     && { ASS(_isSome); return std::move(_elem); }
  A      & unwrap()      & { ASS(_isSome); return           _elem ; }

  OptionalBase(OptionalBase      & a) : _isSome(a._isSome) { if (isSome()) { _elem.init(          a .unwrap()); } }
  OptionalBase(OptionalBase     && a) : _isSome(a._isSome) { if (isSome()) { _elem.init(std::move(a).unwrap()); } }
  OptionalBase(OptionalBase const& a) : _isSome(a._isSome) { if (isSome()) { _elem.init(          a .unwrap()); } }

  OptionalBase& operator=(OptionalBase      & a) = default;
  OptionalBase& operator=(OptionalBase     && a) = default;
  OptionalBase& operator=(OptionalBase const& a) = default;


  static OptionalBase fromPtr(A* ptr) 
  { return ptr == nullptr ? OptionalBase() : *ptr; }

  friend bool operator==(OptionalBase const& lhs, OptionalBase const& rhs) 
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
class OptionalBaseRef
{

  A* _elem;
public:

  OptionalBaseRef(          ) : _elem(nullptr) {  }
  OptionalBaseRef(A const* content) : _elem(const_cast<A*>(content)) { }
  OptionalBaseRef(A* content) : _elem(content) { }

  bool isSome() const { return _elem != nullptr;   }

  A const& unwrap() const& { ASS(isSome()); return           *_elem ; }
  A     && unwrap()     && { ASS(isSome()); return std::move(*_elem); }
  A      & unwrap()      & { ASS(isSome()); return           *_elem ; }

  OptionalBaseRef(OptionalBaseRef      & a) = default;
  OptionalBaseRef(OptionalBaseRef     && a) = default;
  OptionalBaseRef(OptionalBaseRef const& a) = default;

  OptionalBaseRef& operator=(OptionalBaseRef      & a) = default;
  OptionalBaseRef& operator=(OptionalBaseRef     && a) = default;
  OptionalBaseRef& operator=(OptionalBaseRef const& a) = default;

  static OptionalBaseRef fromPtr(A* ptr) 
  { return ptr == nullptr ? OptionalBaseRef() : *ptr; }

  friend bool operator==(OptionalBaseRef const& lhs, OptionalBaseRef const& rhs) 
  { return lhs._elem == rhs._elem; }
};

template<class A>
class OptionalBase<A const&> : public OptionalBaseRef<A>
{
public:
  OptionalBase() : OptionalBaseRef<A>() {}
  OptionalBase(A const& item) : OptionalBaseRef<A>(&item) {}
  OptionalBase(OptionalBase const& b) : OptionalBaseRef<A>(b) {}
};

template<class A>
class OptionalBase<A&> : public OptionalBaseRef<A>
{
public:
  OptionalBase() : OptionalBaseRef<A>() {}
  OptionalBase(A& item) : OptionalBaseRef<A>(&item) {}
  OptionalBase(OptionalBase const& b) : OptionalBaseRef<A>(b) {}
};

// template<class A>
// class OptionalBase<A&>
// {
//
//   A* _elem;
// public:
//
//   OptionalBase() : _elem(nullptr) {}
//   OptionalBase(A      & content) : _elem(&content) { }
//
//   bool isSome() const { return _elem != nullptr;   }
//
//   A const& unwrap() const& { ASS(isSome()); return           *_elem ; }
//   A     && unwrap()     && { ASS(isSome()); return std::move(*_elem); }
//   A      & unwrap()      & { ASS(isSome()); return           *_elem ; }
//
//   OptionalBase(OptionalBase      & a) = default;
//   OptionalBase(OptionalBase     && a) = default;
//   OptionalBase(OptionalBase const& a) = default;
//
//   OptionalBase& operator=(OptionalBase      & a) = default;
//   OptionalBase& operator=(OptionalBase     && a) = default;
//   OptionalBase& operator=(OptionalBase const& a) = default;
//
//   static OptionalBase fromPtr(A* ptr) 
//   { return ptr == nullptr ? OptionalBase() : *ptr; }
//
//   friend bool operator==(OptionalBase const& lhs, OptionalBase const& rhs) 
//   { return lhs._elem == rhs._elem; }
// };

template<class A>
class Optional : OptionalBase<A> {

  Optional(OptionalBase<A>&& base) : OptionalBase<A>(std::move(base)) {  }
public:
  using Content = A;
  using OptionalBase<A>::OptionalBase;
  using OptionalBase<A>::isSome;
  using OptionalBase<A>::unwrap;

  friend bool operator==(Optional const& lhs, Optional const& rhs) 
  { return static_cast<OptionalBase<A>const&>(lhs) == static_cast<OptionalBase<A>const&>(rhs); }

  friend bool operator!=(Optional const& lhs, Optional const& rhs) 
  { return !(lhs == rhs); }

  template<class C>
  static Optional<A> fromPtr(C self) 
  { return Optional(OptionalBase<A>::fromPtr(self)); }

  bool isNone() const { return !this->isSome(); }

  template<class Clsr>
  const A& unwrapOrElse(Clsr f) const& { 
    static_assert(std::is_same<typename std::result_of<Clsr()>::type,
                               A const&                             >::value, "closuer must return reference in order to be memory safe");
    if (this->isSome()) {
      return this->unwrap();
    } else {
      return f();
    }
  }

  template<class Clsr>
  A unwrapOrElse(Clsr f) && { 
    // static_assert(std::is_same<typename std::result_of<Clsr()>::type,
    //                            A &&                             >::value, "closuer must return reference in order to be memory safe");
    if (this->isSome()) {
      return this->unwrap();
    } else {
      return f();
    }
  }

  template<class Clsr>
  A& unwrapOrElse(Clsr f) & { 
    static_assert(std::is_same<typename std::result_of<Clsr()>::type,
                               A &                             >::value, "closuer must return reference in order to be memory safe");
    if (this->isSome()) {
      return this->unwrap();
    } else {
      return f();
    }
  }

  template<class Clsr>
  const A& unwrapOrInit(Clsr f) { 
    if (isNone()) {
      ::new(this) Optional(f());
    }
    return this->unwrap();
  }


  const A& unwrapOr(const A& alternative) const { 
    if (this->isSome()) {
      return this->unwrap();
    } else {
      return alternative;
    }
  }

  // TODO get rid or R here
  template<class R, class CasePresent, class CaseNone>
  R match(CasePresent present, CaseNone none) const { 
    if (this->isSome()) {
      return present(this->unwrap());
    } else {
      return none();
    }
  }

  template<class CasePresent, class CaseNone, class R>
  R match(CasePresent present, CaseNone none) { 
    if (this->isSome()) {
      return present(this->unwrap());
    } else {
      return none();
    }
  }

#define ref_polymorphic(REF, MOVE)                                                                            \
                                                                                                              \
  template<class Clsr>                                                                                        \
  Optional<typename std::result_of<Clsr(A REF)>::type> map(Clsr clsr) REF {                                   \
    using OptOut = Optional<typename std::result_of<Clsr(A REF)>::type>;                                      \
    return this->isSome() ? OptOut(clsr(MOVE(this->unwrap())))                                                \
                          : OptOut();                                                                         \
  }                                                                                                           \
                                                                                                              \
  template<class B> Optional<B> innerInto() REF { return map([](A REF inner) { return B(MOVE(inner)); }); }   \

  FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic

  template<class Clsr>
  typename std::result_of<Clsr(A const&)>::type andThen(Clsr clsr) const& { 
    using OptOut = typename std::result_of<Clsr(A const&)>::type;
    return this->isSome() ? clsr(this->unwrap())
                    : OptOut();
  }



  template<class Clsr>
  typename std::result_of<Clsr(A &&)>::type andThen(Clsr clsr) && { 
    using OptOut = typename std::result_of<Clsr(A &&)>::type;
    return this->isSome() ? clsr(std::move(this->unwrap()))
                    : OptOut();
  }


  template<class Clsr>
  typename std::result_of<Clsr(A &)>::type andThen(Clsr clsr) & { 
    using OptOut = typename std::result_of<Clsr(A &)>::type;
    using OptOut = typename Optional<std::result_of<Clsr(A &)>>::type;
    return this->isSome() ? clsr(this->unwrap())
                    : OptOut();
  }

  friend std::ostream& operator<<(std::ostream& out, Optional const& self) 
  { return self.isSome() ?  out << self.unwrap() : out << "None"; }


};

template<class T> Optional<T> some(T const& t) { return Optional<T>(t);            }
template<class T> Optional<T> some(T     && t) { return Optional<T>(std::move(t)); }
template<class T> Optional<T> some(T      & t) { return Optional<T>(t);            }

template<class T>
Optional<T> none() 
{ return Optional<T>(); }

template<class T>
Optional<T> optionalFromPtr(T* t) 
{ return Optional<T>::fromPtr(t); }

}

#endif // __OPTIONAL_H__
