#ifndef __LIB_EITHER__H__
#define __LIB_EITHER__H__

#define MACRO_EXPANSION true

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Hash.hpp"
#include <memory>
#include <functional>

namespace Lib {

#define FOR_REF_QUALIFIER(macro)                                                                                        \
  macro(const &, ) macro(&, ) macro(&&, std::move)

template <class... As> class Coproduct {
  unsigned _tag;

public:
};

template <> class Coproduct<> {
public:
  static constexpr unsigned size = 0;
};

template <unsigned idx, class A> struct Inj {
  using inner_t = A;
  A _value;
  Inj(A &value) : _value(value) {}
  Inj(A const &value) : _value(value) {}
  Inj(A &&value) : _value(std::move(value)) {}
};

template <class... As> union VariadicUnion;

template <unsigned idx, class... As> struct va_idx;

template <class A, class... As> struct va_idx<0, A, As...> { using type = A; };

template <unsigned idx, class A, class... As> struct va_idx<idx, A, As...> {
  using type = typename va_idx<idx - 1, As...>::type;
};

template <unsigned idx, class... As> struct __unwrap {};

template <class A, class... As> struct __unwrap<0, A, As...> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
  A REF operator()(VariadicUnion<A, As...> REF self) const {                                                            \
    return MOVE(self._head);                                                                                            \
  }

  FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic
};

template <unsigned idx, class A, class... As> struct __unwrap<idx, A, As...> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
  typename va_idx<idx - 1, As...>::type REF operator()(                                                                 \
      VariadicUnion<A, As...> REF self) const {                                                                         \
    return __unwrap<idx - 1, As...>{}(MOVE(self._tail));                                                                \
  }

  FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic
};

template <unsigned idx, class... As> struct init {};

template <class A, class... As> struct init<0, A, As...> {
  void operator()(VariadicUnion<A, As...> &self,
                  typename va_idx<0, A, As...>::type &&value) const {
    // self._head = std::move(value._head);
    ::new (&self._head) A(std::move(value));
  }
};

template <unsigned idx, class A, class... As> struct init<idx, A, As...> {
  void operator()(VariadicUnion<A, As...> &self,
                  typename va_idx<idx, A, As...>::type &&value) const {
    init<idx - 1, As...>{}(self._tail, std::move(value));
  }
};

template <> union VariadicUnion<> {
  void unwrap(unsigned idx) { ASSERTION_VIOLATION_REP(idx) }
  ~VariadicUnion() {}
  void destroy(unsigned idx) { ASSERTION_VIOLATION_REP(idx) }

#define ref_polymorphic(REF, MOVE)                                                                                      \
                                                                                                                        \
  template <class R, class F> R applyPoly(unsigned idx, F f) REF {                                                      \
    ASSERTION_VIOLATION_REP(idx)                                                                                        \
  }                                                                                                                     \
  void init(unsigned idx, VariadicUnion REF other) {                                                                    \
    ASSERTION_VIOLATION_REP(idx)                                                                                        \
  }                                                                                                                     \
                                                                                                                        \
  template <class R> R apply(unsigned idx) REF{ASSERTION_VIOLATION_REP(idx)}

  FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic

  static bool equal(unsigned idx, const VariadicUnion &lhs,
                    const VariadicUnion &rhs) {
    ASSERTION_VIOLATION_REP(idx)
  }
};

template <class A, class... As> union VariadicUnion<A, As...> {
  A _head;
  VariadicUnion<As...> _tail;
  ~VariadicUnion() {}
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

#define ref_polymorphic(REF, MOVE)                                                                                      \
  template <class R, class F> inline R applyPoly(unsigned idx, F f) REF {                                               \
    if (idx == 0) {                                                                                                     \
      return f(MOVE(_head));                                                                                            \
    } else {                                                                                                            \
      return MOVE(_tail).template applyPoly<R>(idx - 1, f);                                                             \
    }                                                                                                                   \
  }                                                                                                                     \
                                                                                                                        \
  template <class R, class F, class... Fs>                                                                              \
  inline R apply(unsigned idx, F f, Fs... fs) REF {                                                                     \
    if (idx == 0) {                                                                                                     \
      return f(MOVE(_head));                                                                                            \
    } else {                                                                                                            \
      return MOVE(_tail).template apply<R>(idx - 1, fs...);                                                             \
    }                                                                                                                   \
  }                                                                                                                     \
  void init(unsigned idx, VariadicUnion REF other) {                                                                    \
    if (idx == 0) {                                                                                                     \
      ::new (&_head) A(MOVE(other._head));                                                                              \
    } else {                                                                                                            \
      MOVE(_tail).init(idx - 1, MOVE(other._tail));                                                                     \
    }                                                                                                                   \
  }

  FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic
  static bool equal(unsigned idx, const VariadicUnion &lhs,
                    const VariadicUnion &rhs) {
    if (idx == 0) {
      return lhs._head == rhs._head;
    } else {
      return VariadicUnion<As...>::equal(idx - 1, lhs._tail, rhs._tail);
    }
  }

  template <unsigned idx, class... Bs> friend struct init;
  VariadicUnion() {}
};


template <class B, class A, class... As> struct idx_of {
  static constexpr unsigned value = idx_of<B, As...>::value + 1;
};

template <class A, class... As> struct idx_of<A, A, As...> { 
  static constexpr unsigned value = 0; 
};

template<class... Ords> struct CoproductOrdering;
template<template<class> class Ord> struct PolymorphicCoproductOrdering;

template <class A, class... As> class Coproduct<A, As...> 
{
  unsigned _tag;

  VariadicUnion<A, As...> _content;
  using Self = Coproduct<A, As...>;

public:
  static constexpr unsigned size = Coproduct<As...>::size + 1;

  template <unsigned idx> struct type {
    using value = typename va_idx<idx, A, As...>::type;
  };
  template <unsigned idx> bool is() const {
    static_assert(idx < size, "out of bounds");
    return _tag == idx;
  }

  template <unsigned idx>
  static Coproduct variant(typename va_idx<idx, A, As...>::type &&value) {
    return Coproduct(
        Inj<idx, typename va_idx<idx, A, As...>::type>(std::move(value)));
  }

  template <unsigned idx>
  static Coproduct variant(const typename va_idx<idx, A, As...>::type &value) {
    return Coproduct(Inj<idx, typename va_idx<idx, A, As...>::type>(value));
  }

  template <unsigned idx>
  static Coproduct variant(typename va_idx<idx, A, As...>::type &value) {
    return Coproduct(Inj<idx, typename va_idx<idx, A, As...>::type>(value));
  }

  template <unsigned idx>
  Coproduct(Inj<idx, typename va_idx<idx, A, As...>::type> &&value)
      : _tag(idx) {
    CALL("Coproduct::Coprodct(Inj<...>&&)")
    static_assert(idx < size, "out of bounds");
    init<idx, A, As...>{}(_content, std::move(value._value));
  }


  // TODO: get rid of the type parameter Ret here.
#define REF_POLYMORPIHIC(REF, MOVE)                                                                                     \
  template <class Ret, class... F> inline Ret match(F... fs) REF {                                                      \
    ASS_REP(_tag <= size, _tag);                                                                                        \
    return MOVE(_content).template apply<Ret>(_tag, fs...);                                                             \
  }                                                                                                                     \
  template <class Ret, class F> inline Ret collapsePoly(F f) REF {                                                      \
    ASS_REP(_tag <= size, _tag);                                                                                        \
    return MOVE(_content).template applyPoly<Ret>(_tag, f);                                                             \
  }                                                                                                                     \
  template <class... F> inline Coproduct map(F... fs) REF {                                                             \
    return match<Coproduct>(fs...);                                                                                     \
  }                                                                                                                     \
                                                                                                                        \
  Coproduct &operator=(Coproduct REF other) {                                                                           \
    CALL("Coproduct& operator=(Coproduct " #REF "other)")                                                               \
    ASS_REP(other._tag <= size, other._tag);                                                                            \
    _content.destroy(_tag);                                                                                             \
    _content.init(other._tag, MOVE(other._content));                                                                    \
    _tag = other._tag;                                                                                                  \
    return *this;                                                                                                       \
  }                                                                                                                     \
                                                                                                                        \
  Coproduct(Coproduct REF other) : _tag(other._tag) {                                                                   \
    CALL("Coproduc(Coproduct " #REF " other)")                                                                          \
    ASS_REP(other._tag <= size, other._tag);                                                                            \
    _content.init(other._tag, MOVE(other._content));                                                                    \
  }                                                                                                                     \
                                                                                                                        \
  template<class B>                                                                                                     \
  explicit Coproduct(B REF b)                                                                                           \
    : Coproduct(variant<idx_of<B, A, As...>::value>(MOVE(b)))                                                           \
  { }                                                                                                                   \
                                                                                                                        \
  template <class B> inline B REF as() REF {                                                                            \
    /* TODO static assertions */                                                                                        \
    return unwrap<idx_of<B, A, As...>::value>();                                                                        \
  }                                                                                                                     \
                                                                                                                        \
  template <unsigned idx>                                                                                               \
  inline typename va_idx<idx, A, As...>::type REF unwrap() REF {                                                        \
    CALL("Coproduct::unwrap() " #REF );                                                                                 \
    static_assert(idx < size, "out of bounds");                                                                         \
    ASS_EQ(idx, _tag);                                                                                                  \
    return __unwrap<idx, A, As...>{}(MOVE(_content));                                                                   \
  }

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs) {
    if (lhs._tag != rhs._tag) {
      return false;
    } else {
      return VariadicUnion<A, As...>::equal(lhs._tag, lhs._content,
                                            rhs._content);
    }
  }

  friend bool operator!=(const Coproduct &lhs, const Coproduct &rhs) {
    return !(lhs == rhs);
  }
  ~Coproduct() { _content.destroy(_tag); }

private:
  struct __writeToStream {
    unsigned _tag;
    std::ostream &out;
    template <class B> std::ostream &operator()(const B &b) {
      return out << "Coproduct<" << _tag << ">(" << b << ")";
    }
  };

public:

  friend std::ostream &operator<<(std::ostream &out, const Coproduct &self) {
    return self.template collapsePoly<std::ostream &>(__writeToStream{self._tag, out});
  }
  friend struct std::hash<Coproduct>;

  template<class... Ords> friend struct CoproductOrdering;

}; // class Coproduct<A, As...> 


namespace TypeList {

#define MP(f, ...) typename f < __VA_ARGS__ >:: result

  template<class... As>
  struct TypeList;

  template<template<class...> class HKT, class A> 
  struct Into;

  template<template<class...> class HKT, class... As> 
  struct Into<HKT, TypeList<As...> >
  { using result = HKT<As...>; };

  template<class A, class B> 
  struct Concat;

  template<class... As, class... Bs> 
  struct Concat<TypeList<As...>, TypeList<Bs...>>
  { using result = TypeList<As..., Bs...>; };


  template<class ZipFn, class A, class B>
  struct Zip;

  template<class ZipFn>
  struct Zip<ZipFn, TypeList<>, TypeList<>>
  { using result = TypeList<>; };


  template<class ZipFn, class A, class... As, class B, class... Bs>
  struct Zip<ZipFn, TypeList<A, As...>, TypeList<B, Bs...> >
  {
    using result = MP(Concat, TypeList<typename std::result_of<ZipFn(A, B)>::type>, MP(Zip, ZipFn, TypeList<As...>, TypeList<Bs...>));
  };

  template<unsigned i, class A> struct Get;

  template<class A, class... As> struct Get<0, TypeList<A, As...>>
  { using result = A; };

  template<unsigned i, class A, class... As> struct Get<i, TypeList<A, As...>>
  { using result = MP(Get, i - 1, TypeList<As...>); };

} // namespace TypeList


}

#include "Optional.hpp"

namespace Lib {
  
using namespace TypeList;


template<unsigned idx>
struct TryUnwrap
{
  template<class... As>
  static Optional<Coproduct<As...>> apply(Coproduct<As...> c)
  { 
    if (c._tag == idx) return some(Coproduct<As...>::template variant<idx>(c.template unwrap<idx>()));
    else return TryUnwrap<idx - 1>::apply(c);
  }
};

template<>
struct TryUnwrap<0>
{
  template<class... As>
  static Optional<MP(Get, 0, TypeList<As...>)> apply(Coproduct<As...> c)
  { 
    if (c._tag == 0) return some(c.template unwrap<0>());
    ASSERTION_VIOLATION
  }
};



template<unsigned n, unsigned m> struct ZipHelper 
{
  template<class ZipFn, class... As>
  static Optional<MP(Into, Coproduct, MP(Zip, ZipFn, TypeList<As const&...>, TypeList<As const&...>))> apply(
        ZipFn zipFn,
        Coproduct<As...> const& lhs, 
        Coproduct<As...> const& rhs)
  {
    using Result = MP(Into, Coproduct, MP(Zip, ZipFn, TypeList<As const&...>, TypeList<As const&...>));

    if (lhs.template is<n>()) {
      return some(Result::template variant<n>(zipFn(
              lhs.template unwrap<n>(),
              rhs.template unwrap<n>()
            )));
    }
    else return ZipHelper<n + 1, m>::apply(zipFn, lhs, rhs);
  }
};

template<unsigned n> struct ZipHelper<n, n> 
{
  template<class ZipFn, class... As>
  static Optional<MP(Into, Coproduct, MP(Zip, ZipFn, TypeList<As const&...>, TypeList<As const&...>))> apply(
        ZipFn zipFn,
        Coproduct<As...> const& lhs, 
        Coproduct<As...> const& rhs)
  { ASSERTION_VIOLATION }
};


template<class ZipFn, class... As>
Optional<MP(Into, Coproduct, MP(Zip, ZipFn, TypeList<As const&...>, TypeList<As const&...>))> zipWith(
      ZipFn zipFn,
      Coproduct<As...> const& lhs, 
      Coproduct<As...> const& rhs)
{
  constexpr unsigned sz = Coproduct<As...>::size;
  return ZipHelper<0, sz>::template apply<ZipFn, As...>(zipFn, lhs, rhs);
}

template<class F>
struct PairFn 
{
  F f;
  template<class A, class B>
  typename std::result_of<F(A,B)>::type operator()(const std::pair<const A&,const B&>& elems) const
  { return f(std::get<0>(elems), std::get<1>(elems));  }
};

template<class F>
PairFn<F> pairFn(F f) { return { f }; }

struct ConstPair {
  template<class A, class B>
  std::pair<const A&, const B&> operator()(const A& a, const B& b) const 
  { return std::pair<A const&, B const&>(a,b); }
};

template<class... Ords> struct CoproductOrdering 
{
  template<class... As>
  bool operator()(Coproduct<As...> const& lhs, Coproduct<As...> const& rhs) const
  { 
    CALL("CoproductOrdering::operator()(Coproduct<As...> const&, Coproduct<As...> const&)")
    if (lhs._tag < rhs._tag) return true;
    if (lhs._tag > rhs._tag) return false;

    return zipWith(ConstPair{}, lhs, rhs).unwrap()
        .template match<bool>(pairFn(Ords{})...);
  }
};


template<template<class> class Ord> struct PolymorphicCoproductOrdering
{
  template<class... As>
  bool operator()(Coproduct<As...> const& lhs, Coproduct<As...> const& rhs) const
  { return CoproductOrdering<Ord<As>...>{}(lhs,rhs); }
};


} // namespace Lib

struct __PolyHash {
  template<class T>
  size_t operator()(T const& t) const
  { return std::hash<T>{}(t); }
};

template<class... Ts> struct std::hash<Lib::Coproduct<Ts...>>
{
  size_t operator()(Lib::Coproduct<Ts...> const& self) const 
  { 

    return Lib::HashUtils::combine(std::hash<unsigned>{}(self._tag), self.template collapsePoly<size_t>(__PolyHash{})); 
  }
};


template<class... As>
struct std::less<Lib::Coproduct<As...> >
{
  bool operator()(const Lib::Coproduct<As...>& lhs, const Lib::Coproduct<As...>& rhs)
  { return Lib::PolymorphicCoproductOrdering<std::less>{}(lhs,rhs); }
};


#endif // __LIB_EITHER__H__
