#ifndef __LIB_COPRODUCT__H__
#define __LIB_COPRODUCT__H__

#define MACRO_EXPANSION true

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Hash.hpp"
#include "Lib/TypeList.hpp"
#include <memory>
#include <functional>

namespace Lib {

#define FOR_REF_QUALIFIER(macro)                                                                                        \
  macro(const &, ) macro(&, ) macro(&&, std::move)

namespace TL = TypeList;

template <class... As> 
class Coproduct;


namespace CoproductImpl {

  template <class... As> union VariadicUnion;
  template <unsigned idx, class As> struct Unwrap;

  template <> union VariadicUnion<> {
    CLASS_NAME(VariadicUnion)

    void unwrap(unsigned idx) { ASSERTION_VIOLATION_REP(idx) }
    ~VariadicUnion() {}
    void destroy(unsigned idx) { ASSERTION_VIOLATION_REP(idx) }

#define ref_polymorphic(REF, MOVE)                                                                                      \
                                                                                                                        \
    template <class R, class F> R applyPoly(unsigned idx, F f) REF {                                                    \
      ASSERTION_VIOLATION_REP(idx)                                                                                      \
    }                                                                                                                   \
                                                                                                                        \
    template <class R> R apply(unsigned idx) REF{ASSERTION_VIOLATION_REP(idx)}

    FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic

    static bool equal(unsigned idx, const VariadicUnion &lhs, const VariadicUnion &rhs) {
      ASSERTION_VIOLATION_REP(idx)
    }
  };

  template <class A, class... As> union VariadicUnion<A, As...> {
    CLASS_NAME(VariadicUnion)
    // USE_ALLOCATOR(VariadicUnion)
    using Ts = TL::List<A,As...>;

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
    template <class R, class F> inline R applyPoly(unsigned idx, F f) REF {                                             \
      if (idx == 0) {                                                                                                   \
        return f(MOVE(_head));                                                                                          \
      } else {                                                                                                          \
        return MOVE(_tail).template applyPoly<R>(idx - 1, f);                                                           \
      }                                                                                                                 \
    }                                                                                                                   \
                                                                                                                        \
    template <class R, class F, class... Fs>                                                                            \
    inline R apply(unsigned idx, F f, Fs... fs) REF {                                                                   \
      if (idx == 0) {                                                                                                   \
        return f(MOVE(_head));                                                                                          \
      } else {                                                                                                          \
        return MOVE(_tail).template apply<R>(idx - 1, fs...);                                                           \
      }                                                                                                                 \
    }                                                                                                                   \

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

    template <unsigned idx, class Bs> friend struct InitStaticTag;
    VariadicUnion() {}
  };

  template <class A, class... As> struct Unwrap<0, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    A REF operator()(VariadicUnion<A, As...> REF self) const {                                                          \
      return MOVE(self._head);                                                                                          \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

  template <unsigned idx, class A, class... As> struct Unwrap<idx, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    TL::Get<idx - 1, TL::List<As...>> REF operator()(                                                                   \
        VariadicUnion<A, As...> REF self) const {                                                                       \
      return Unwrap<idx - 1, TL::List<As...>>{}(MOVE(self._tail));                                                      \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic
  };


  template <unsigned idx, class As> struct InitStaticTag {};

  template <class A, class... As> struct InitStaticTag<0, TL::List<A, As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<0, TL::List<A, As...>> REF value) const                      \
    { ::new (&self._head) A(MOVE(value)); }                                                                             \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

  template <unsigned idx, class A, class... As> struct InitStaticTag<idx, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<idx, TL::List<A, As...>> REF value) const                    \
    { InitStaticTag<idx - 1, TL::List<As...>>{}(self._tail, MOVE(value)); }                                             \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  template <unsigned acc, unsigned size, class As> struct InitDynamicTag;

  template <unsigned size, class... As> struct InitDynamicTag<size, size, TL::List<As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const                     \
    {  ASSERTION_VIOLATION }                                                                                            \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  template <unsigned acc, unsigned size, class... As> struct InitDynamicTag<acc, size, TL::List<As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                                      \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const                     \
    {                                                                                                                   \
      using Ts = TL::List<As...>;                                                                                       \
      auto unwrap = Unwrap<acc, Ts>{};                                                                                  \
      if (acc == idx) {                                                                                                 \
        ::new (&self) TL::Get<acc,Ts>(unwrap(MOVE(value)));                                                             \
        return;                                                                                                         \
      }                                                                                                                 \
      InitDynamicTag<acc + 1, size, TL::List<As...>>{}(self, idx, MOVE(value));                                         \
    }                                                                                                                   \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

}

template<class... Ords> struct CoproductOrdering;
template<template<class> class Ord> struct PolymorphicCoproductOrdering;

template <class A, class... As> 
class Coproduct<A, As...> 
{
  unsigned _tag;

  CoproductImpl::VariadicUnion<A, As...> _content;
  using Self = Coproduct<A, As...>;
  using Content = decltype(_content);

  /** unsafe default constructor. tag as well as content will be uninit */
  Coproduct() {}

public:
  CLASS_NAME(Coproduct)
  // USE_ALLOCATOR(Coproduct)

  using Ts = TL::List<A, As...>;
  static constexpr unsigned size = TL::Size<Ts>::val;

  unsigned tag() const { return _tag; }

  template <unsigned idx> struct type 
  {
    using value = TL::Get<idx, TL::List<A, As...>>;
  };

  template <unsigned idx> bool is() const {
    static_assert(idx < size, "out of bounds");
    return _tag == idx;
  }

  template <class B> bool is() const {
    return _tag == TL::IdxOf<B, Ts>::val;
  }


  template<class... Bs> using FstTy = TL::Get<0, TL::List<Bs...>>;
  // TODO: get rid of the type parameter Ret here.
#define REF_POLYMORPIHIC(REF, MOVE)                                                                                     \
                                                                                                                        \
  Coproduct(Coproduct REF other) : _tag(other._tag) {                                                                   \
    CALL("Coproduct(Coproduct " #REF " other)")                                                                         \
    ASS_REP(other._tag <= size, other._tag);                                                                            \
    CoproductImpl::InitDynamicTag<0, size, Ts>{}(_content, other._tag, MOVE(other._content));                           \
  }                                                                                                                     \
                                                                                                                        \
  template <unsigned idx>                                                                                               \
  static Coproduct variant(TL::Get<idx, Ts> REF value) {                                                                \
    Coproduct self;                                                                                                     \
    self._tag = idx;                                                                                                    \
    CoproductImpl::InitStaticTag<idx, Ts>{}(self._content, MOVE(value));                                                \
    return MOVE(self);                                                                                                  \
  }                                                                                                                     \
                                                                                                                        \
  template <class... F>                                                                                                 \
  inline ResultOf<FstTy<F...>, A REF> match(F... fs) REF {                                                              \
    using Ret = ResultOf<FstTy<F...>, A REF>;                                                                           \
    ASS_REP(_tag <= size, _tag);                                                                                        \
    return MOVE(_content).template apply<Ret>(_tag, fs...);                                                             \
  }                                                                                                                     \
  template <class F>                                                                                                    \
  inline ResultOf<F, A REF> apply(F f) REF {                                                                            \
    ASS_REP(_tag <= size, _tag);                                                                                        \
    return MOVE(_content).template applyPoly<ResultOf<F, A REF>>(_tag,f);                                               \
  }                                                                                                                     \
  template <class... F> inline Coproduct map(F... fs) REF {                                                             \
    return match(fs...);                                                                                                \
  }                                                                                                                     \
                                                                                                                        \
  Coproduct &operator=(Coproduct REF other) {                                                                           \
    CALL("Coproduct& operator=(Coproduct " #REF "other)")                                                               \
    ASS_REP(other._tag <= size, other._tag);                                                                            \
    _content.destroy(_tag);                                                                                             \
    CoproductImpl::InitDynamicTag<0, size, Ts>{}(_content, other._tag, MOVE(other._content));                           \
    _tag = other._tag;                                                                                                  \
    return *this;                                                                                                       \
  }                                                                                                                     \
                                                                                                                        \
  template<class B>                                                                                                     \
  explicit Coproduct(B REF b)                                                                                           \
    : Coproduct(variant<TL::IdxOf<B, Ts>::val>(MOVE(b)))                                                                \
  { }                                                                                                                   \
                                                                                                                        \
  template <class B> inline B REF unwrap() REF {                                                                        \
    return MOVE(unwrap<TL::IdxOf<B, Ts>::val>());                                                                       \
  }                                                                                                                     \
                                                                                                                        \
  template <unsigned idx>                                                                                               \
  inline TL::Get<idx, Ts> REF unwrap() REF {                                                                            \
    CALL("Coproduct::unwrap() " #REF );                                                                                 \
    static_assert(idx < size, "out of bounds");                                                                         \
    ASS_EQ(idx, _tag);                                                                                                  \
    return CoproductImpl::Unwrap<idx, Ts>{}(MOVE(_content));                                                            \
  }

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  // TODO: replace with zipping
  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs) {
    if (lhs._tag != rhs._tag) {
      return false;
    } else {
      return Content::equal(lhs._tag, lhs._content, rhs._content);
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
    return self.apply(__writeToStream{self._tag, out});
  }
  friend struct std::hash<Coproduct>;

  template<class... Ords> friend struct CoproductOrdering;
}; // class Coproduct<A, As...> 


}

#include "Optional.hpp"

namespace Lib {
  
namespace TL = TypeList;


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
  static Optional<TL::Get<0, TL::List<As...>>> apply(Coproduct<As...> c)
  { 
    if (c._tag == 0) return some(c.template unwrap<0>());
    ASSERTION_VIOLATION
  }
};



template<unsigned n, unsigned m> struct ZipHelper 
{
  template<class ZipFn, class... As>
  static Optional<TL::Into<Coproduct, TL::Zip<ZipFn, TL::List<As const&...>, TL::List<As const&...>>>> apply(
        ZipFn zipFn,
        Coproduct<As...> const& lhs, 
        Coproduct<As...> const& rhs)
  {
    using Result = TL::Into<Coproduct, TL::Zip<ZipFn, TL::List<As const&...>, TL::List<As const&...>>>;

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
  static Optional<TL::Into<Coproduct, TL::Zip<ZipFn, TL::List<As const&...>, TL::List<As const&...>>>> apply(
        ZipFn zipFn,
        Coproduct<As...> const& lhs, 
        Coproduct<As...> const& rhs)
  { ASSERTION_VIOLATION }
};


template<class ZipFn, class... As>
Optional<TL::Into<Coproduct, TL::Zip<ZipFn, TL::List<As const&...>, TL::List<As const&...>>>> zipWith(
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
        .match(pairFn(Ords{})...);
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

    return Lib::HashUtils::combine(std::hash<unsigned>{}(self._tag), self.apply(__PolyHash{})); 
  }
};


template<class... As>
struct std::less<Lib::Coproduct<As...> >
{
  bool operator()(const Lib::Coproduct<As...>& lhs, const Lib::Coproduct<As...>& rhs)
  { return Lib::PolymorphicCoproductOrdering<std::less>{}(lhs,rhs); }
};


#endif // __LIB_COPRODUCT__H__
