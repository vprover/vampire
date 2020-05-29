#ifndef __LIB_EITHER__H__
#define __LIB_EITHER__H__

#include <memory>
#include "Debug/Tracer.hpp"
#include "Debug/Assertion.hpp"

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

  explicit Either(const Either& other) : _tag(other._tag)
  {
      if (other._tag == Left) {
        new(&_cont._left) A(other._cont._left);
      } else {
        new(&_cont._right) B(other._cont._right);
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


template<class... As>
class Coproduct {
  unsigned _tag;
public:
};

template<>
class Coproduct<> {
public:
  static constexpr unsigned size = 0;
};

template<unsigned idx, class A>
struct Inj {
  using inner_t = A;
  A _value;
  // Inj(A value) : _value(value){}   
  Inj(A&& value) : _value(std::move(value)){}   
};

template<class... As>
union VariadicUnion;

template<unsigned idx, class... As>
struct va_idx;

template<class A, class... As>
struct va_idx<0, A, As...> {
  using type = A;
};

template<unsigned idx, class A, class... As>
struct va_idx<idx, A, As...> {
  using type = typename va_idx<idx - 1, As...>::type;
};


template<unsigned idx, class... As>
struct __unwrap {
};

template<class A, class... As>
struct __unwrap<0, A, As...> {
  A& operator()(VariadicUnion<A, As...>& self) const {
    return self._head;
  }
  const A& operator()(const VariadicUnion<A, As...>& self) const {
    return self._head;
  }
};

template<unsigned idx,class A, class... As>
struct __unwrap<idx, A, As...> {
  typename va_idx<idx - 1 , As...>::type& operator()(VariadicUnion<A, As...>& self) const {
    return __unwrap<idx-1, As...>{}(self._tail);
  }
  const typename va_idx<idx - 1 , As...>::type& operator()(const VariadicUnion<A, As...>& self) const {
    return __unwrap<idx-1, As...>{}(self._tail);
  }
};

template<unsigned idx, class... As>
struct init {
};

template<class A, class... As>
struct init<0, A, As...> {
  void operator()(VariadicUnion<A, As...>& self, typename va_idx<0, A, As...>::type&& value) const {
    // self._head = std::move(value._head);
    ::new(&self._head)A(std::move(value));
  }
};

template<unsigned idx, class A, class... As>
struct init<idx, A, As...> { void operator()(VariadicUnion<A, As...>& self, typename va_idx<idx, A, As...>::type&& value) const {
    init<idx - 1, As...>{}(self._tail, std::move(value));
  }
};

template<>
union VariadicUnion<> {
  void unwrap(unsigned idx) {
    ASSERTION_VIOLATION_REP(idx)
  }
  ~VariadicUnion() {}
  void destroy(unsigned idx) {
    ASSERTION_VIOLATION_REP(idx)
  }
  void initClone(unsigned idx, const VariadicUnion& other) {
    ASSERTION_VIOLATION_REP(idx)
  }
  void initMove(unsigned idx, VariadicUnion&& other) {
    ASSERTION_VIOLATION_REP(idx)
  }
  static bool equal(unsigned idx, const VariadicUnion& lhs, const VariadicUnion& rhs) {
    ASSERTION_VIOLATION_REP(idx)
  }
};


template<class A, class... As>
union VariadicUnion<A, As...> {
  A _head;
  VariadicUnion<As...> _tail;
  ~VariadicUnion() { }
  VariadicUnion<A, As...> clone(unsigned idx) {
    VariadicUnion out;
    if (idx == 0) {
      out._head = this->_head;
    } else {
      out._tail = _tail.clone(idx);
    }
    return out;
  }  

  void destroy(unsigned idx) {
    if (idx == 0) {
      _head.~A();
    } else {
      _tail.destroy(idx - 1);
    }
  }

  void initClone(unsigned idx, const VariadicUnion& other) {
    if (idx == 0) {
      ::new(&_head) A(other._head);
    } else {
      _tail.initClone(idx - 1, other._tail);
    }
  }

  void initMove(unsigned idx, VariadicUnion&& other) {
    if (idx == 0) {
      ::new(&_head) A(std::move(other._head));
    } else {
      _tail.initMove(idx - 1, std::move(other._tail));
    }
  }


  static bool equal(unsigned idx, const VariadicUnion& lhs, const VariadicUnion& rhs) {
    if (idx == 0) {
      return lhs._head == rhs._head;
    } else {
      return VariadicUnion<As...>::equal(idx - 1, lhs._tail,rhs._tail);
    }
  }

  template<unsigned idx, class...Bs>
  friend struct init;
  VariadicUnion(){}
};


template<class A, class... As>
class Coproduct<A, As...> {
  unsigned _tag;

  VariadicUnion<A, As...> _content;
  using Self = Coproduct<A,As...>;
public:
  static constexpr unsigned size = Coproduct<As...>::size + 1;

  template<unsigned idx>
  struct type {
    using value = typename va_idx<idx, A, As...>::type;
  };

  template<unsigned idx> bool is() const
  { static_assert(idx < size, "out of bounds"); return _tag == idx; }

  template<unsigned idx> 
  typename va_idx<idx, A, As...>::type& unwrap()
  { 
    static_assert(idx < size, "out of bounds"); 
    ASS(idx == _tag); 
    return __unwrap<idx, A, As...>{}(_content);
  }

  template<unsigned idx> 
  const typename va_idx<idx, A, As...>::type& unwrap() const
  { 
    static_assert(idx < size, "out of bounds"); 
    ASS(idx == _tag); 
    return __unwrap<idx, A, As...>{}(_content);
  }

  template<unsigned idx> 
  static Coproduct variant(typename va_idx<idx, A, As...>::type&& value) {
    return Coproduct(Inj<idx, typename va_idx<idx, A, As...>::type>(std::move(value)));
  }

  Self& operator=(const Self& other) {
    _content.destroy(_tag);
    _tag = other._tag;
    _content.initClone(_tag, other._content);
  }

  template<unsigned idx>
  Coproduct(Inj<idx, typename va_idx<idx, A, As...>::type>&& value) : _tag(idx) 
  {
    CALL("Coproduct::Coprodct(Inj<...>&&)")
    init<idx, A, As...>{}(_content, std::move(value._value));
  }

  friend bool operator==(const Coproduct& lhs, const Coproduct& rhs) {
    if (lhs._tag != rhs._tag) {
      return false;
    } else {
      return VariadicUnion<A, As...>::equal(lhs._tag, lhs._content, rhs._content);
    }
  }

  friend bool operator!=(const Coproduct& lhs, const Coproduct& rhs) {
    return !( lhs == rhs );
  }

  Coproduct& operator=(Coproduct&& other) {
    CALL("Coproduct& operator=(Coproduct&& other)")
    _content.destroy(_tag);
    _content.initMove(other._tag, std::move(other._content));
    _tag = other._tag;
    return *this;
  }

  Coproduct(const Coproduct& other) : _tag(other._tag) {
    _content.initClone(other._tag, other._content);
  }

  Coproduct(Coproduct&& other) : _tag(other._tag) {
    CALL("Coproduc(Coproduct&& other)")
    _content.initMove(other._tag, std::move(other._content));
  }

  ~Coproduct() {
    _content.destroy(_tag);
  }

};

}
#endif // __LIB_EITHER__H__
