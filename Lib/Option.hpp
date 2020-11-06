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
     Value() {};
    ~Value() {};
  } _elem;

   MaybeUninit() : _elem() {}
  ~MaybeUninit() {}
#define methods(ref, mv)                                                                                      \
  operator T ref() ref                                                                                        \
  { return mv(_elem.init); }                                                                                  \
                                                                                                              \
  void init(T ref content)                                                                                    \
  { ::new(&_elem)T(mv(content)); }                                                                            \
                                                                                                              \
  MaybeUninit& operator=(T ref content)                                                                       \
  {                                                                                                           \
    _elem.init = mv(content);                                                                                 \
    return *this;                                                                                             \
  }                                                                                                           \

  FOR_REF_QUALIFIER(methods)

#undef methods 
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

#define for_ref_qualifier(ref, mv)                                                                            \
  explicit OptionBase(A ref content)                                                                          \
    : _isSome(true)                                                                                           \
      , _elem()                                                                                               \
  {                                                                                                           \
    CALL("Option(A " #ref ")")                                                                                \
    _elem.init(mv(content));                                                                                  \
  }                                                                                                           \
                                                                                                              \
  A ref unwrap() ref                                                                                          \
  {                                                                                                           \
    ASS(_isSome);                                                                                             \
    return mv(_elem);                                                                                         \
  }                                                                                                           \
                                                                                                              \
  OptionBase(OptionBase ref a) : _isSome(a._isSome)                                                           \
  {                                                                                                           \
    CALL("OptionBase(OptionBase " #ref ")");                                                                  \
    if (isSome()) {                                                                                           \
      _elem.init(mv(a).unwrap());                                                                             \
    }                                                                                                         \
  }                                                                                                           \
                                                                                                              \
  OptionBase& operator=(OptionBase ref other)                                                                 \
  {                                                                                                           \
    CALL("OptionBase& operator=(OptionBase "#ref")");                                                         \
                                                                                                              \
    if (_isSome) {                                                                                            \
      if (other._isSome) {                                                                                    \
        unwrap() = mv(other).unwrap();                                                                        \
      } else {                                                                                                \
        unwrap().~A();                                                                                        \
      }                                                                                                       \
    } else {                                                                                                  \
      ASS(isNone())                                                                                           \
      if (other._isSome){                                                                                     \
         _elem.init(mv(other).unwrap());                                                                      \
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
  { return lhs._elem == rhs._elem; }
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

template<class A>
class Option : OptionBase<A> {

  explicit Option(OptionBase<A>&& base) : OptionBase<A>(std::move(base)) {  }
public:
  using Content = A;
  using OptionBase<A>::OptionBase;
  using OptionBase<A>::isSome;
  using OptionBase<A>::unwrap;

  friend bool operator==(Option const& lhs, Option const& rhs) 
  { return static_cast<OptionBase<A>const&>(lhs) == static_cast<OptionBase<A>const&>(rhs); }

  friend bool operator!=(Option const& lhs, Option const& rhs) 
  { return !(lhs == rhs); }

  template<class C>
  static Option<A> fromPtr(C self) 
  { return Option(OptionBase<A>::fromPtr(self)); }

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
      ::new(this) Option(f());
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
  Option<typename std::result_of<Clsr(A REF)>::type> map(Clsr clsr) REF {                                     \
    using OptOut = Option<typename std::result_of<Clsr(A REF)>::type>;                                        \
    return this->isSome() ? OptOut(clsr(MOVE(this->unwrap())))                                                \
                          : OptOut();                                                                         \
  }                                                                                                           \
                                                                                                              \
  template<class B> Option<B> innerInto() REF { return map([](A REF inner) { return B(MOVE(inner)); }); }     \
                                                                                                              \
  template<class Clsr>                                                                                        \
  typename std::result_of<Clsr(A REF)>::type andThen(Clsr clsr) REF {                                         \
    using OptOut = typename std::result_of<Clsr(A REF)>::type;                                                \
    return this->isSome() ? clsr(MOVE(*this).unwrap())                                                        \
                          : OptOut();                                                                         \
  }

  FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic



  friend std::ostream& operator<<(std::ostream& out, Option const& self) 
  { return self.isSome() ?  out << self.unwrap() : out << "None"; }


};

template<class T> Option<T> some(T const& t) { return Option<T>(t);            }
template<class T> Option<T> some(T     && t) { return Option<T>(std::move(t)); }
template<class T> Option<T> some(T      & t) { return Option<T>(t);            }

template<class T>
Option<T> none() 
{ return Option<T>(); }

template<class T>
Option<T> optionalFromPtr(T* t) 
{ return Option<T>::fromPtr(t); }

}

#endif // __OPTIONAL_H__
