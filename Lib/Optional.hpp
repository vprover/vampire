#ifndef __OPTIONAL_H__
#define __OPTIONAL_H__

#include "Lib/Either.hpp"


namespace Lib {

template<class A>
class Optional {
  struct Unit {};
  Coproduct<A, Unit> _self;
  Optional(Coproduct<A, Unit> self) : _self(self) {}
public:

  Optional() : _self(Coproduct<A,Unit>::template variant<1>(Unit{})) {}
  Optional(A&& content) : _self(Coproduct<A,Unit>::template variant<0>(std::move(content))) {}

  bool isSome() const { return _self.template is<0>();  }
  bool isNone() const { return _self.template is<1>();  }
  const A& unwrap() const { return _self.template unwrap<0>();  }

  template<class Clsr>
  const A& unwrapOrElse(Clsr f) const { 
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

};

}

#endif // __OPTIONAL_H__
