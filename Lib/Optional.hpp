#ifndef __OPTIONAL_H__
#define __OPTIONAL_H__

#include "Lib/Coproduct.hpp"
#include <type_traits>


namespace Lib {

template<class A>
class Optional {
  struct Unit {};
  Coproduct<A, Unit> _self;
  Optional(Coproduct<A, Unit> self) : _self(self) {}
public:

  Optional() : _self(Coproduct<A,Unit>::template variant<1>(Unit{})) {}
  Optional(A     && content) : _self(Coproduct<A,Unit>::template variant<0>(std::move(content))) {}
  Optional(A      & content) : _self(Coproduct<A,Unit>::template variant<0>(          content )) {}
  Optional(A const& content) : _self(Coproduct<A,Unit>::template variant<0>(          content )) {}

  bool isSome() const { return _self.template is<0>();  }
  bool isNone() const { return _self.template is<1>();  }
  A const& unwrap() const& { return _self.template unwrap<0>();  }
  A     && unwrap()     && { return std::move(_self.template unwrap<0>());  }
  A      & unwrap()      & { return _self.template unwrap<0>();  }

  template<class Clsr>
  const A& unwrapOrElse(Clsr f) const& { 
    static_assert(std::is_same<typename std::result_of<Clsr()>::type,
                               A const&                             >::value, "closuer must return reference in order to be memory safe");
    if (isSome()) {
      return unwrap();
    } else {
      return f();
    }
  }

  static Optional fromPtr(A* ptr) 
  { return ptr == nullptr ? Optional() : *ptr; }

  template<class Clsr>
  A unwrapOrElse(Clsr f) && { 
    // static_assert(std::is_same<typename std::result_of<Clsr()>::type,
    //                            A &&                             >::value, "closuer must return reference in order to be memory safe");
    if (isSome()) {
      return unwrap();
    } else {
      return f();
    }
  }

  template<class Clsr>
  A& unwrapOrElse(Clsr f) & { 
    static_assert(std::is_same<typename std::result_of<Clsr()>::type,
                               A &                             >::value, "closuer must return reference in order to be memory safe");
    if (isSome()) {
      return unwrap();
    } else {
      return f();
    }
  }

  template<class Clsr>
  const A& unwrapOrInit(Clsr f) { 
    if (isNone()) {
      _self = Coproduct<A,Unit>::template variant<0>(f());
    }
    return unwrap();
  }


  const A& unwrapOr(const A& alternative) const { 
    if (isSome()) {
      return unwrap();
    } else {
      return alternative;
    }
  }

  template<class R, class CasePresent, class CaseNone>
  R match(CasePresent present, CaseNone none) const { 
    if (isSome()) {
      return present(unwrap());
    } else {
      return none();
    }
  }

  template<class CasePresent, class CaseNone, class R>
  R match(CasePresent present, CaseNone none) { 
    if (isSome()) {
      return present(unwrap());
    } else {
      return none();
    }
  }

  template<class Clsr>
  Optional<typename std::result_of<Clsr(A &&)>::type> map(Clsr clsr) && { 
    using OptOut = Optional<typename std::result_of<Clsr(A &&)>::type>;
    return isSome() ? OptOut(clsr(std::move(unwrap())))
                    : OptOut();
  }

  template<class Clsr>
  typename std::result_of<Clsr(A const&)>::type andThen(Clsr clsr) const& { 
    using OptOut = typename std::result_of<Clsr(A const&)>::type;
    return isSome() ? clsr(unwrap())
                    : OptOut();
  }



  template<class Clsr>
  typename std::result_of<Clsr(A &&)>::type andThen(Clsr clsr) && { 
    using OptOut = typename std::result_of<Clsr(A &&)>::type;
    return isSome() ? clsr(std::move(unwrap()))
                    : OptOut();
  }


  template<class Clsr>
  typename std::result_of<Clsr(A &)>::type andThen(Clsr clsr) & { 
    using OptOut = typename std::result_of<Clsr(A &)>::type;
    using OptOut = typename Optional<std::result_of<Clsr(A &)>>::type;
    return isSome() ? clsr(unwrap())
                    : OptOut();
  }

};

template<class T> Optional<T> some(T const& t) { return Optional<T>(t);            }
template<class T> Optional<T> some(T     && t) { return Optional<T>(std::move(t)); }
template<class T> Optional<T> some(T      & t) { return Optional<T>(t);            }

template<class T>
Optional<T> none() 
{ return Optional<T>(); }

template<class T> Optional<T> 
optionalFromPtr(T* t) 
{ return Optional<T>::fromPtr(t); }

}

#endif // __OPTIONAL_H__
