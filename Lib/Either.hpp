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
  Ret collapse(Fl l, Fr r)const  {
    switch (_tag) {
      case Left:
        return l(_cont._left);
      case Right: 
        return r(_cont._right);
    }
  }

  template<class Fl, class Fr> 
  void match(Fl l, Fr r) const {
    switch (_tag) {
      case Left:
        return l(_cont._left);
      case Right: 
        return r(_cont._right);
    }
  }


  template<class Fr> 
  A toLeft(Fr r) const {
    switch (_tag) {
      case Left:
        return _cont._left;
      case Right: 
        return r(_cont._right);
    }
  }


  template<class Fl> 
  B toRight(Fl l) const {
    switch (_tag) {
      case Left:
        return l(_cont._left);
      case Right: 
        return _cont._right;
    }
  }

  template<class Fl, class Fr> 
  Either map(Fl l, Fr r) const {
    switch (_tag) {
      case Left:
        return l(_cont._left);
      case Right: 
        return r(_cont._right);
    }
  }

  static Either<A,B> left(A l) {
    return Either(l);
  }

  static Either<A,B> right(B r) {
    return Either(r);
  }

  ~Either() {
    switch(_tag) {
      case Left:
        _cont._left.~A();
        break;
      case Right:
        _cont._right.~B();
        break;
    }
  }

  Either(Either&& l) : _tag(l._tag), _cont(std::move(l._cont)) {}
  Either(const Either& l) : _tag(l._tag), _cont(l._cont) {}
  friend void operator<<(std::ostream& out, const Either& self) {
    return self.collapse<std::ostream&>(
        [&](A x){return out << x;},
        [&](B x){return out << x;}
        );
  }

  // Either(A left) : _cont(left), _tag(Left) {}
  // Either(B right) : _cont(right), _tag(Right) {}
private:

  enum Tag {
    Left,
    Right,
  };
  Tag _tag;
  union Content {
    A _left;
    B _right;
    ~Content() {}
    Content(A left) : _left(left){}
    Content(B right) : _right(right){}
    // Content(Content&& c) = default;
  } _cont;

  Either(A lft) : _tag(Left), _cont(lft) {}
  Either(B rght) : _tag(Right), _cont(rght) {}
};




}
#endif // __LIB_EITHER__H__
