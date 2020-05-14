#ifndef __LIB_EITHER__H__
#define __LIB_EITHER__H__

#include <memory>

namespace Lib {


// template<class A, class B>
// union Either {
// private:
//
//   enum Tag {
//     Left,
//     Right,
//   };
//
//   A unwrapLeft()  {
//     ASS(tag() == Left);
//     return _left._value;
//   }
//   A unwrapRight()  {
//     ASS(tag() == Right);
//     return _right._value;
//   }
//   bool isLeft() const {
//     return tag() == Left;
//   }
//
//   Either(int, A left) : _left{Left, left} {}
//   Either(void*, B right) : _right{Right, right} {}
//
//   Tag tag() const {
//     return _left.tag();
//   }
//
//   struct {Tag _tag; A _value;} _left;
//   struct {Tag _tag; B _value;} _right;
//
// public:
//
//   template<class Ret, class Fl, class Fr> 
//   Ret collapse(Fl l, Fr r)const  {
//     return isLeft() 
//       ? l(unwrapLeft())
//       : r(unwrapRight());
//     }
//
//   template<class Fl, class Fr> 
//   void match(Fl l, Fr r) const {
//     return collapse<void,Fl,Fr>(l,r);
//   }
//
//
//   template<class Fr> 
//   A toLeft(Fr r) const {
//     return collapse<A>([](A a) { return a; }, r);
//   }
//
//
//   template<class Fl> 
//   B toRight(Fl l) const {
//     return collapse<B>(l, [](B x) { return x; });
//   }
//
//   template<class Fl, class Fr> 
//   Either map(Fl l, Fr r) const {
//     return collapse<Either>(l, r);
//   }
//
//   static Either<A,B> left(A left) {
//     return Either(int(0), left);
//   }
//
//   static Either<A,B> right(B right) {
//     return Either((void*)(0), right);
//   }
//
//   ~Either() {
//     if (isLeft()) {
//       _left._value.~A();
//     } else {
//       _right._value.~B();
//     }
//   }
//
//
// };

template<class A, class B>
class Either {
public:

  A unwrapLeft() {
    ASS(_tag == Left);
    return _cont._left;
  }

  B unwrapRight() {
    ASS(_tag == Right);
    return _cont._right;
  }

  template<class Ret, class Fl, class Fr> 
  Ret collapse(Fl l, Fr r) const  {
    switch (_tag) {
      case Left:
        return l(std::move(_cont._left));
      case Right: 
        return r(std::move(_cont._right));
#if VDEBUG
      case Uninit:
        ASSERTION_VIOLATION
#endif
    }
  }

  template<class Ret, class Fl, class Fr> 
  Ret collapse(Fl l, Fr r) {
    switch (_tag) {
      case Left:
        return l(std::move(_cont._left));
      case Right: 
        return r(std::move(_cont._right));
#if VDEBUG
      case Uninit:
        ASSERTION_VIOLATION
#endif
    }
  }

  template<class Fl, class Fr> 
  void match(Fl l, Fr r) const {
    return collapse<void>(l,r);
  }

  template<class Fl, class Fr> 
  void match(Fl l, Fr r) {
    return collapse<void>(l,r);
  }


  template<class Fr> 
  A toLeft(Fr r) const {
    return collapse<A>([](A x) {return x; }, r);
  }

  template<class Fr> 
  A toLeft(Fr r) {
    return collapse<A>([](A x) {return x; }, r);
  }

  template<class Fl> 
  B toRight(Fl l) const {
    return collapse<B>(l, [](B x) {return x; });
  }

  template<class Fl> 
  B toRight(Fl l) {
    return collapse<B>(l, [](B x) {return x; });
  }


  template<class Fl, class Fr> 
  Either map(Fl l, Fr r) const {
    return collapse<Either>(l,r);
  }

  template<class Fl, class Fr> 
  Either map(Fl l, Fr r) {
    return collapse<Either>(l,r);
  }

  static Either<A,B> left(A l) {
    return Either(l);
  }

  static Either<A,B> right(B r) {
    return Either(r);
  }

  static Either<A,B> uninit() {
    return Either();
  }

  ~Either() {
    switch(_tag) {
      case Left:
        _cont._left.~A();
        break;
      case Right:
        _cont._right.~B();
        break;
#if VDEBUG
      case Uninit:
        ASSERTION_VIOLATION
#endif
    }
  }

  Either(Either&& other) : _tag(other._tag)
    {
      if (other._tag == Left) {
        _cont = std::move(other._cont._left);
      } else {
        _cont = std::move(other._cont._right);
      }
    }
  Either& operator=(Either&& other) {
    _tag = other._tag;
    if (other._tag == Left) {
      _cont = std::move(other._cont._left);
    } else {
      _cont = std::move(other._cont._right);
    }
    return *this;
  }
  friend std::ostream& operator<<(std::ostream& out, const Either& self) {
    return self.collapse<std::ostream&>(
        [&](const A& a) { return out << "Left(" << a << ")"; },
        [&](const B& b) { return out << "Right(" << b << ")"; }
        );
  }
  Either() 
#if VDEBUG
    : _tag(Uninit) 
#endif
  {}
private:

  enum Tag {
    Left,
    Right,
#if VDEBUG
    Uninit,
#endif 
  };
  Tag _tag;
  union Content {
    A _left;
    B _right;
    Content() {}
    ~Content() {}
    Content(A left) : _left(left){}
    Content(B right) : _right(right){}
    Content(A&& left) : _left(std::move(left)){}
    Content(B&& right) : _right(std::move(right)){}
    Content& operator=(A&& left) { _left = std::move(left); return *this; }
    Content& operator=(B&& right) { _right = std::move(right); return *this; }
    // Content(Content&& c) = default;
  } _cont;

  Either(A lft) : _tag(Left), _cont(lft) {}
  Either(B rght) : _tag(Right), _cont(rght) {}
};




}
#endif // __LIB_EITHER__H__
