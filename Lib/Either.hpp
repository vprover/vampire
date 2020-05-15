#ifndef __LIB_EITHER__H__
#define __LIB_EITHER__H__

#include <memory>

namespace Lib {


template<class A, class B>
class Either {

  struct Move{};
  struct Copy{};

public:
  using left_t = A;
  using right_t = B;

  bool isRight() const {
    return _tag == Right;
  }

  bool isLeft() const {
    return _tag == Left;
  }

  A& unwrapLeft() {
    ASS(_tag == Left);
    return _cont._left;
  }

  B& unwrapRight() {
    ASS(_tag == Right);
    return _cont._right;
  }


  const A& unwrapLeft() const {
    ASS(_tag == Left);
    return _cont._left;
  }

  const B& unwrapRight() const {
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
    }
  }

  template<class Ret, class Fl, class Fr> 
  Ret collapse(Fl l, Fr r) {
    switch (_tag) {
      case Left:
        return l(std::move(_cont._left));
      case Right: 
        return r(std::move(_cont._right));
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

  static Either<A,B> rightMv(B&& r) {
    return Either(std::move(r), Move{});
  }

  static Either<A,B> leftMv(A&& l) {
    return Either(std::move(l), Move{});
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
    }
  }

  Either(Either&& other) //: _tag(other._tag)
    {
      if (other._tag == Left) {
        new(this) Either(std::move(other._cont._left), Move{});
      } else {
        new(this) Either(std::move(other._cont._right), Move{});
      }
    }
  Either& operator=(Either&& other) {
    CALL("Either::opearator=(Either&& other)")
    DBG("Either::opearator=(Either&& other)")
    if (_tag == other._tag) {
      switch (_tag) {
        case Left:
          _cont.mvAsgn(std::move(other._cont._left));
          break;

        case Right:
          _cont.mvAsgn(std::move(other._cont._right));
          break;
      }
    } else {
      switch (_tag) {

        case Left:
          _cont._left.~A();
          new(this) Either(std::move(other._cont._right), Move{});
          break;

        case Right:
          _cont._right.~B();
          new(this) Either(std::move(other._cont._left), Move{});
          break;

      }
    }
    return *this;
  }
  friend std::ostream& operator<<(std::ostream& out, const Either& self) {
    switch (self._tag) {
      case Left:
        return out << "Left(" << self._cont._left << ")";
      case Right:
        return out << "Right(" << self._cont._right << ")";
    }
  }
  Either() : Either(A(), Move{}) {}
  // {
  //   DBG("Either::Either()")
  //     Debug::Tracer::printStack(std::cout);
  // }
private:

  enum Tag {
    Left,
    Right,
  };
  Tag _tag;
  union Content {
    A _left;
    B _right;
    Content() {}
    ~Content() {}
    Content(A&& left) : _left(std::move(left)){}
    Content(B&& right) : _right(std::move(right)){}
    Content(A left) : _left(left){}
    Content(B right) : _right(right){}
    Content(A&& left, Move) : _left(std::move(left)){}
    Content(B&& right, Move) : _right(std::move(right)){}
    Content& mvAsgn(A&& left) { _left = std::move(left); return *this; }
    Content& mvAsgn(B&& right) { _right = std::move(right); return *this; }
  } _cont;

  Either(A&& lft, Move) : _tag(Left), _cont(std::move(lft), Move{}) {}
  Either(B&& rght, Move) : _tag(Right), _cont(std::move(rght), Move{}) {}
  Either(A lft, Copy) : _tag(Left), _cont(lft) {}
  Either(B rght, Copy) : _tag(Right), _cont(rght) {}
  Either(A&& lft) : _tag(Left), _cont(std::move(lft)) {}
  Either(B&& rght) : _tag(Right), _cont(std::move(rght)) {}
  Either(A lft) : _tag(Left), _cont(lft) {}
  Either(B rght) : _tag(Right), _cont(rght) {}
};




}
#endif // __LIB_EITHER__H__
