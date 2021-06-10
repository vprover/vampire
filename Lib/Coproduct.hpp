/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

/**
 * This file defines the class Coproduct, which is a generic tagged union. 
 *
 * \see UnitTests/tCoproduct.cpp  for usage
 */
#ifndef __LIB_COPRODUCT__H__
#define __LIB_COPRODUCT__H__

#define MACRO_EXPANSION true

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Hash.hpp"
#include "Lib/TypeList.hpp"
#include "Lib/Option.hpp"
#include <memory>
#include <functional>

#define SAME(...) std::is_same<__VA_ARGS__>::value // TODO

namespace Lib {

  template<class A> struct rm_ref            { using type = A; };
  template<class A> struct rm_ref<A      &>  { using type = A; };
  template<class A> struct rm_ref<A const&>  { using type = A; };
  template<class A> struct rm_ref<A     &&>  { using type = A; };
  template<class A> using rm_ref_t = typename rm_ref<A>::type;

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
#define ref_polymorphic(REF, MOVE)                                                                            \
                                                                                                              \
    template <class R, class F> R apply(unsigned idx, F f) REF                                         \
    { ASSERTION_VIOLATION_REP(idx) }                                                                          \
                                                                                                              \
    template <class R, class... F>                                                                            \
    static R match2(unsigned idx, VariadicUnion REF lhs, VariadicUnion REF rhs, F... f)                \
    { ASSERTION_VIOLATION_REP(idx) }                                                                          \
                                                                                                              \
    template <class R> R match(unsigned idx) REF{ASSERTION_VIOLATION_REP(idx)}                         \

    FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic

    void destroy(unsigned idx) {ASSERTION_VIOLATION_REP(idx)}
    static bool equal(unsigned idx, VariadicUnion const& lhs, VariadicUnion const& rhs) {ASSERTION_VIOLATION_REP(idx)}
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

#define ref_polymorphic(REF, MOVE)                                                                            \
    template <class R, class F> R apply(unsigned idx, F f) REF {                                       \
      if (idx == 0) {                                                                                         \
        return f(MOVE(_head));                                                                                \
      } else {                                                                                                \
        return MOVE(_tail).template apply<R>(idx - 1, f);                                                     \
      }                                                                                                       \
    }                                                                                                         \
                                                                                                              \
    template <class R, class F, class... Fs>                                                                  \
    R match(unsigned idx, F f, Fs... fs) REF {                                                         \
      if (idx == 0) {                                                                                         \
        return f(MOVE(_head));                                                                                \
      } else {                                                                                                \
        return MOVE(_tail).template match<R>(idx - 1, fs...);                                                 \
      }                                                                                                       \
    }                                                                                                         \
                                                                                                              \
    template <class R, class F, class... Fs>                                                                  \
    static R match2(unsigned idx, VariadicUnion REF lhs, VariadicUnion REF rhs, F f, Fs... fs)         \
    {                                                                                                         \
      if (idx == 0) {                                                                                         \
        return f(MOVE(lhs._head), MOVE(rhs._head));                                                           \
      } else {                                                                                                \
        return VariadicUnion<As...>::template match2<R>(idx - 1, MOVE(lhs._tail), MOVE(rhs._tail), fs...);    \
      }                                                                                                       \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic

    void destroy(unsigned idx) 
    { 
      if (idx == 0) {
        _head.~A(); 
      } else {
        _tail.destroy(idx - 1);
      }
    }

    static bool equal(unsigned idx, VariadicUnion const& lhs, VariadicUnion const& rhs) {
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
#define ref_polymorphic(REF, MOVE)                                                                            \
    A REF operator()(VariadicUnion<A, As...> REF self) const {                                                \
      return MOVE(self._head);                                                                                \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

  template <unsigned idx, class A, class... As> struct Unwrap<idx, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                            \
    TL::Get<idx - 1, TL::List<As...>> REF operator()(                                                         \
        VariadicUnion<A, As...> REF self) const {                                                             \
      return Unwrap<idx - 1, TL::List<As...>>{}(MOVE(self._tail));                                            \
    }

    FOR_REF_QUALIFIER(ref_polymorphic)
#undef ref_polymorphic
  };


  template <unsigned idx, class As> struct InitStaticTag {};

  template <class A, class... As> struct InitStaticTag<0, TL::List<A, As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                            \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<0, TL::List<A, As...>> REF value) const            \
    { ::new (&self._head) A(MOVE(value)); }                                                                   \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };

  template <unsigned idx, class A, class... As> struct InitStaticTag<idx, TL::List<A, As...>> {
#define ref_polymorphic(REF, MOVE)                                                                            \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<idx, TL::List<A, As...>> REF value) const          \
    { InitStaticTag<idx - 1, TL::List<As...>>{}(self._tail, MOVE(value)); }                                   \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  template <unsigned acc, unsigned size, class As> struct InitDynamicTag;

  template <unsigned size, class... As> struct InitDynamicTag<size, size, TL::List<As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                            \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const           \
    {  ASSERTION_VIOLATION }                                                                                  \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };


  template <unsigned acc, unsigned size, class... As> struct InitDynamicTag<acc, size, TL::List<As...>> 
  {
#define ref_polymorphic(REF, MOVE)                                                                            \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const           \
    {                                                                                                         \
      using Ts = TL::List<As...>;                                                                             \
      auto unwrap = Unwrap<acc, Ts>{};                                                                        \
      if (acc == idx) {                                                                                       \
        ::new (&self) TL::Get<acc,Ts>(unwrap(MOVE(value)));                                                   \
        return;                                                                                               \
      }                                                                                                       \
      InitDynamicTag<acc + 1, size, TL::List<As...>>{}(self, idx, MOVE(value));                               \
    }                                                                                                         \

    FOR_REF_QUALIFIER(ref_polymorphic)

#undef ref_polymorphic
  };
}

template<class... Ords> struct CoproductOrdering;
template<template<class> class Ord> struct PolymorphicCoproductOrdering;

/** 
 * the actual Coproduct class.  
 * A coproduct, also called Sum type, is a set of types, tagged with indices. It can be constructed with 
 * either of the type/index pairs, and in this implementation the index can be left away if all types in this 
 * coproduct are distinct. 
 *
 * It is implemented as a tagged union.
 * 
 * \see UnitTests/tCoproduct.cpp for usage
 */
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

  /** a type-level list of all types of this Coproduct */
  using Ts = TL::List<A, As...>;

  /** the number of alternatives */
  static constexpr unsigned size = TL::Size<Ts>::val;

  unsigned tag() const { return _tag; }

public:

  /** Returns whether this coproduct is the variant idx */
  template<unsigned idx> bool is() const 
  {
    static_assert(idx < size, "out of bounds");
    return _tag == idx;
  }

  /** 
   * Returns whether this coproduct is the variant witht he given type. 
   * \pre is exactly one occurence of the type B in this Coproduct's types (A,As...).
   */
  template <class B> bool is() const 
  { return _tag == TL::IdxOf<B, Ts>::val; }

  /** helper type level function, returning the first type of a list of types */
  template<class... Bs> using FstTy = TL::Get<0, TL::List<Bs...>>;

#define REF_POLYMORPIHIC(REF, MOVE)                                                                           \
                                                                                                              \
  Coproduct(Coproduct REF other) : _tag(other._tag) {                                                         \
    CALL("Coproduct(Coproduct " #REF " other)")                                                               \
    ASS_REP(other._tag <= size, other._tag);                                                                  \
    CoproductImpl::InitDynamicTag<0, size, Ts>{}(_content, other._tag, MOVE(other._content));                 \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * constructs a new Coproduct with the variant idx. The argument type must match `idx`th type of this       \
   * corpoduct's variants types (A,As...).                                                                    \
   */                                                                                                         \
  template <unsigned idx>                                                                                     \
  static Coproduct variant(TL::Get<idx, Ts> REF value) {                                                      \
    Coproduct self;                                                                                           \
    self._tag = idx;                                                                                          \
    CoproductImpl::InitStaticTag<idx, Ts>{}(self._content, MOVE(value));                                      \
    return self;                                                                                              \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * constructs a new Coproduct with the variant idx.                                                         \
   * \pre B must occur exactly once in A,As...                                                                \
   */                                                                                                         \
  template<class B>                                                                                           \
  explicit Coproduct(B REF b)                                                                                 \
    : Coproduct(variant<TL::IdxOf<B, Ts>::val>(MOVE(b)))                                                      \
  { }                                                                                                         \
                                                                                                              \
   /**                                                                                                        \
   * transforms all variants of this Coproduct to the same type and retuns the result                         \
   *                                                                                                          \
   * The arguments F... must all be function whichs argument type must match the type of the corresponding    \
   * variant of this Coproduct. The output types of the functions must all be the same type, which will be    \
   * the return type of this function.                                                                        \
   */                                                                                                         \
  template <class... F>                                                                                       \
  ResultOf<FstTy<F...>, A REF> match(F... fs) REF {                                                    \
    using Ret = ResultOf<FstTy<F...>, A REF>;                                                                 \
    ASS_REP(_tag <= size, _tag);                                                                              \
    return MOVE(_content).template match<Ret>(_tag, fs...);                                                   \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * transforms all variants of this Coproduct to the same type and retuns the result                         \
   *                                                                                                          \
   * This function works basically in the same way as match, but takes one polymorphic function object that   \
   * can transform any variant instead of multiple functions per variant.                                     \
   */                                                                                                         \
  template <class F>                                                                                          \
  ResultOf<F, A REF> apply(F f) REF {                                                                  \
    ASS_REP(_tag <= size, _tag);                                                                              \
    return MOVE(_content).template apply<ResultOf<F, A REF>, F>(_tag,f);                          \
  }                                                                                                           \
                                                                                                              \
  Coproduct &operator=(Coproduct REF other) {                                                                 \
    CALL("Coproduct& operator=(Coproduct " #REF "other)")                                                     \
    ASS_REP(other._tag <= size, other._tag);                                                                  \
    _content.destroy(_tag);                                                                                   \
    CoproductImpl::InitDynamicTag<0, size, Ts>{}(_content, other._tag, MOVE(other._content));                 \
    _tag = other._tag;                                                                                        \
    return *this;                                                                                             \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is of another type       \
   * the result is undefined.                                                                                 \
   *                                                                                                          \
   * \pre B must occur exactly once in A,As...                                                                \
   */                                                                                                         \
  template <class B> B REF unwrap() REF                                                                \
  { return MOVE(unwrap<TL::IdxOf<B, Ts>::val>()); }                                                           \
                                                                                                              \
  /**                                                                                                         \
   * returns the value of this Coproduct if its variant's index is idx. otherwise the result is undefined.    \
   *                                                                                                          \
   * \pre idx must be less than the number of variants of this Coproduct                                      \
   */                                                                                                         \
  template <unsigned idx>                                                                                     \
  TL::Get<idx, Ts> REF unwrap() REF {                                                                  \
    CALL("Coproduct::unwrap() " #REF );                                                                       \
    static_assert(idx < size, "out of bounds");                                                               \
    ASS_EQ(idx, _tag);                                                                                        \
    return CoproductImpl::Unwrap<idx, Ts>{}(MOVE(_content));                                                  \
  }                                                                                                           \
                                                                                                              \
  /**                                                                                                         \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is of another type       \
   * an empty Option is returned.                                                                             \
   *                                                                                                          \
   * \pre B must occur exactly once in A,As...                                                                \
   */                                                                                                         \
  template <class B> Option<B REF> as() REF                                                            \
  { return is<B>() ? MOVE(*this).template unwrap<B>() : Option<B REF>();  }                                   \
                                                                                                              \
                                                                                                             \
  /**                                                                                                         \
   * returns the value of this Coproduct if its variant's index is idx. otherwise an empty Option is returned.\
   *                                                                                                          \
   * \pre idx must be less than the number of variants of this Coproduct                                      \
   */                                                                                                         \
  template <unsigned idx>                                                                                     \
  Option<TL::Get<idx, Ts> REF> as() REF                                                                \
  { return is<idx>() ? unwrap<idx>() : Option<TL::Get<idx, Ts> REF>();  }                                     \

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  // Option<Coproduct<std::tuple<A&, A&>, std::tuple<As&, As&>...>> zipVariant(Coproduct& other)
  // {
  //   using Co = Coproduct<std::tuple<A&, A&>, std::tuple<As&, As&>...>;
  //   return _content.template apply<Option<Co>>(_tag, [&](auto& inner) {
  //     using T = rm_ref_t<decltype(inner)>;
  //     return other.template as<T>().map([&](T& other) {
  //            return Co(std::tie(inner, other));
  //     });
  //   });
  // }
  //
  // // bool sameVariant(Coproduct const& other) const
  // // { return zipVariant(other).isSome(); }
  //
  // Option<Coproduct<std::tuple<A const&, A const&>, std::tuple<As const&, As const&>...>> zipVariant(Coproduct const& other)
  // const
  // {
  //   using Co = Coproduct<std::tuple<A const&, A const&>, std::tuple<As const&, As const&>...>;
  //   return _content.template apply<Option<Co>>(_tag, [&](auto && inner) {
  //     using T = rm_ref_t<decltype(inner)>;
  //     Option<T const&> o = other.template as<T>();
  //     return std::move(o).map([&](T const& other) {
  //            std::tuple<T const&, T const&> tup = std::make_tuple<T const&, T const&>(inner, other);
  //            return Co(std::move(tup));
  //     });
  //   });
  // }
 
  // bool sameVariant(Coproduct const& other) const
  // { return zipVariant(other).isSome(); }

  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs)
  {
    if (lhs._tag != rhs._tag) {
      return false;
    } else {
      auto tag = lhs._tag;
      return Content::equal(tag, lhs._content, rhs._content);
    }
  }

  friend bool operator!=(const Coproduct &lhs, const Coproduct &rhs)
  { return !(lhs == rhs); }

  ~Coproduct() 
  { _content.destroy(_tag); }

  friend std::ostream &operator<<(std::ostream &out, const Coproduct &self)
  { return self.apply([&](auto const& x)  -> std::ostream&
        { return out << "var" << self._tag << "(" << x << ")"; }); }

  friend struct std::hash<Coproduct>;

  template<class... Ords> friend struct CoproductOrdering;
  friend bool operator<(Coproduct const& lhs, Coproduct const& rhs) 
  { return std::less<Coproduct>{}(lhs,rhs); }

  friend bool operator>(Coproduct const& lhs, Coproduct const& rhs) 
  { return rhs < lhs; }

  friend bool operator<=(Coproduct const& lhs, Coproduct const& rhs) 
  { return lhs < rhs || lhs == rhs; }

  friend bool operator>=(Coproduct const& lhs, Coproduct const& rhs) 
  { return lhs > rhs || lhs == rhs; }

}; // class Coproduct<A, As...> 



namespace TL = TypeList;

template<class... Ords> struct CoproductOrdering 
{
  template<class... As>
  bool operator()(Coproduct<As...> const& lhs, Coproduct<As...> const& rhs) const
  { 
    CALL("CoproductOrdering::operator()(Coproduct<As...> const&, Coproduct<As...> const&)")
    if (lhs._tag < rhs._tag) return true;
    if (lhs._tag > rhs._tag) return false;

    auto tag = lhs._tag;
    return CoproductImpl::VariadicUnion<As...>::template match2<bool>(tag, lhs._content, rhs._content, Ords{}...);
  }
};

template<template<class> class Ord> struct PolymorphicCoproductOrdering
{
  template<class... As>
  bool operator()(Coproduct<As...> const& lhs, Coproduct<As...> const& rhs) const
  { return CoproductOrdering<Ord<As>...>{}(lhs,rhs); }
};

} // Lib

template<class... Ts> struct std::hash<Lib::Coproduct<Ts...>>
{
  size_t operator()(Lib::Coproduct<Ts...> const& self) const
  {
    return Lib::HashUtils::combine(
        std::hash<unsigned>{}(self._tag),
        self.apply([](auto const& x){ return std::hash<Lib::rm_ref_t<decltype(x)>>{}(x); }));
  }
};


template<class... As>
struct std::less<Lib::Coproduct<As...> >
{
  bool operator()(const Lib::Coproduct<As...>& lhs, const Lib::Coproduct<As...>& rhs)
  { return Lib::PolymorphicCoproductOrdering<std::less>{}(lhs,rhs); }
};

#endif // __LIB_COPRODUCT__H__

