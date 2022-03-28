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
 * \see UnitTests/tCoproduct.cpp for a tutorial
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

namespace Lib {

namespace TL = TypeList;

template <class... As> 
class Coproduct;

/** This namespace constains helper classes and functions to implement the coproduct */
namespace CoproductImpl {

  /** This class is an untagged union of all type arguments. It is defined inductively by template specialization. 
   * In a pseudo haskellish syntax the definition of the union can be thought of like this:
   * data VariadicUnion []      = bottom type
   * data VariadicUnion (a::as) = union {a, Coproduct as}
   */
  template <class... As> union VariadicUnion;

  /** Base case of the inductive definition of VariadicUnion. Note that an empty union is an uninhabited type. 
   * This means none of its methods will ever be called.  
   *
   * data VariadicUnion []      = bottom type
   */
  template<> union VariadicUnion<> {
    CLASS_NAME(VariadicUnion)

    inline void unwrap(unsigned idx) { ASSERTION_VIOLATION_REP(idx) }
    ~VariadicUnion() {}
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
                                                                                                              \
    template <class R, class F> inline R apply(unsigned idx, F f) REF                                         \
    { ASSERTION_VIOLATION_REP(idx) }                                                                          \
                                                                                                              \
    template <class R, class... F>                                                                            \
    inline static R match2(unsigned idx, VariadicUnion REF lhs, VariadicUnion REF rhs, F... f)                \
    { ASSERTION_VIOLATION_REP(idx) }                                                                          \
                                                                                                              \
    template <class R> inline R match(unsigned idx) REF{ASSERTION_VIOLATION_REP(idx)}                         \

    FOR_REF_QUALIFIER(for_ref_qualifier)
#undef for_ref_qualifier

    inline void destroy(unsigned idx) {ASSERTION_VIOLATION_REP(idx)}
    inline static bool equal(unsigned idx, VariadicUnion const& lhs, VariadicUnion const& rhs) {ASSERTION_VIOLATION_REP(idx)}
  };

  /** Inductive case of the inductive definition of VariadicUnion.  
   *
   * data VariadicUnion (a::as) = union {a, Coproduct as}
   */
  template <class A, class... As> union VariadicUnion<A, As...> {
    CLASS_NAME(VariadicUnion)
    // USE_ALLOCATOR(VariadicUnion)
    using Ts = TL::List<A,As...>;

    A _head;
    VariadicUnion<As...> _tail;

    ~VariadicUnion() {}

// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
                                                                                                              \
    /** applies the `idx`th function of `F,Fs...` to the contents of this union, interpreting them as the     \
     * `idx`th type of `A,As...`. This is only memory safe if that very type  has indeed been stored in this  \
     * union. */                                                                                              \
    template <class R, class F, class... Fs>                                                                  \
    inline R match(unsigned idx, F f, Fs... fs) REF {                                                         \
      if (idx == 0) {                                                                                         \
        return f(MOVE(_head));                                                                                \
      } else {                                                                                                \
        return MOVE(_tail).template match<R>(idx - 1, fs...);                                                 \
      }                                                                                                       \
    }                                                                                                         \
                                                                                                              \
    /** same as `match`, but using the same function for every type.*/                                        \
    template <class R, class F> inline R apply(unsigned idx, F f) REF {                                       \
      if (idx == 0) {                                                                                         \
        return f(MOVE(_head));                                                                                \
      } else {                                                                                                \
        return MOVE(_tail).template apply<R>(idx - 1, f);                                                     \
      }                                                                                                       \
    }                                                                                                         \
                                                                                                              \
    /** same as `match`, but using applying th function to the contents of two unions at once. both must have \
     * the `idx`th type of `A,As...` stored in them. */                                                       \
    template <class R, class F, class... Fs>                                                                  \
    inline static R match2(unsigned idx, VariadicUnion REF lhs, VariadicUnion REF rhs, F f, Fs... fs)         \
    {                                                                                                         \
      if (idx == 0) {                                                                                         \
        return f(MOVE(lhs._head), MOVE(rhs._head));                                                           \
      } else {                                                                                                \
        return VariadicUnion<As...>::template match2<R>(idx - 1, MOVE(lhs._tail), MOVE(rhs._tail), fs...);    \
      }                                                                                                       \
    }

    FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier

    inline void destroy(unsigned idx) 
    { 
      if (idx == 0) {
        _head.~A(); 
      } else {
        _tail.destroy(idx - 1);
      }
    }

    inline static bool equal(unsigned idx, VariadicUnion const& lhs, VariadicUnion const& rhs) {
      if (idx == 0) {
        return lhs._head == rhs._head;
      } else {
        return VariadicUnion<As...>::equal(idx - 1, lhs._tail, rhs._tail);
      }
    }

    template <unsigned idx, class Bs> friend struct InitStaticTag;
    VariadicUnion() {}

  }; // VariadicUnion

  /** A function object to reinterpret a VariadicUnion as its `idx`th type argument. 
   * `As` is a list of types, as defined in `TypeList::List`. */
  template <unsigned idx, class As> struct Unwrap;

  template <class A, class... As> struct Unwrap<0, TL::List<A, As...>> {
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
    A REF operator()(VariadicUnion<A, As...> REF self) const {                                                \
      return MOVE(self._head);                                                                                \
    }

    FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier
  };

  template <unsigned idx, class A, class... As> struct Unwrap<idx, TL::List<A, As...>> {
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
    TL::Get<idx - 1, TL::List<As...>> REF operator()(                                                         \
        VariadicUnion<A, As...> REF self) const {                                                             \
      return Unwrap<idx - 1, TL::List<As...>>{}(MOVE(self._tail));                                            \
    }

    FOR_REF_QUALIFIER(for_ref_qualifier)
#undef for_ref_qualifier
  };


  /** A function object to initialize a VariadicUnion with its `idx`th type argument, 
   * where `idx` is known at compile time.
   * `As` is a list of types, as defined in `TypeList::List`. */
  template <unsigned idx, class As> struct InitStaticTag {};

  template <class A, class... As> struct InitStaticTag<0, TL::List<A, As...>> 
  {
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<0, TL::List<A, As...>> REF value) const            \
    { ::new (&self._head) A(MOVE(value)); }                                                                   \

    FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier
  };

  template <unsigned idx, class A, class... As> struct InitStaticTag<idx, TL::List<A, As...>> {
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
    void operator()(VariadicUnion<A, As...> &self, TL::Get<idx, TL::List<A, As...>> REF value) const          \
    { InitStaticTag<idx - 1, TL::List<As...>>{}(self._tail, MOVE(value)); }                                   \

    FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier
  };


  /** A function object to initialize a VariadicUnion with its `idx`th type argument, 
   * where `idx` is known only at runtime. `acc` and `size` are being used for bounds checks and to 
   * compare `idx` against them.
   * `As` is a list of types, as defined in `TypeList::List`. */
  template <unsigned acc, unsigned size, class As> struct InitDynamicTag;

  template <unsigned size, class... As> struct InitDynamicTag<size, size, TL::List<As...>> 
  {
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const           \
    {  ASSERTION_VIOLATION }                                                                                  \

    FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier
  };


  template <unsigned acc, unsigned size, class... As> struct InitDynamicTag<acc, size, TL::List<As...>> 
  {
// This macro will b expanded for (REF,MV) in { (`&&`, `std::move`), (`&`, ``), (`const &`, ``) }
#define for_ref_qualifier(REF, MOVE)                                                                          \
    void operator()(VariadicUnion<As...> &self, unsigned idx, VariadicUnion<As...> REF value) const           \
    {                                                                                                         \
      using Ts = TL::List<As...>;                                                                             \
      auto unwrap = Unwrap<acc, Ts>{};                                                                        \
      if (acc == idx) {                                                                                       \
        ::new (&self._head) TL::Get<acc,Ts>(unwrap(MOVE(value)));                                             \
        return;                                                                                               \
      }                                                                                                       \
      InitDynamicTag<acc + 1, size, TL::List<As...>>{}(self, idx, MOVE(value));                               \
    }                                                                                                         \

    FOR_REF_QUALIFIER(for_ref_qualifier)

#undef for_ref_qualifier
  };
} // namespace CoproductImpl

/** a class used to combine orderings `O1...On` for types `A1...An` to a ordering on 
 * Coproduct<A1...An>. This is done by first comparing the tags, and then using the 
 * orderings `O1...On` if the tags are the same. */
template<class... Ords> struct CoproductOrdering;

/** Same as CoproductOrdering, but one polymorphic ordering class `Ord` instead of 
 * multiple orderings `O1...On`. */
template<template<class> class Ord> struct PolymorphicCoproductOrdering;

/** 
 * The actual Coproduct class.  
 * A coproduct, also called Sum type, is a union of types, tagged with indices. It can be constructed with 
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
  /* _tag specifies which of the types in `A, As...` is actually stored in the field _content */
  unsigned _tag;
  CoproductImpl::VariadicUnion<A, As...> _content;

  using Self = Coproduct<A, As...>;
  using Content = decltype(_content);

  /** unsafe default constructor, content will be uninit */
  Coproduct() : _tag(std::numeric_limits<unsigned>::max()) {}

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
  inline ResultOf<FstTy<F...>, A REF> match(F... fs) REF {                                                    \
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
  inline ResultOf<F, A REF> apply(F f) REF {                                                                  \
    ASS_REP(_tag <= size, _tag);                                                                              \
    return MOVE(_content).template apply<ResultOf<F, A REF>>(_tag,f);                                         \
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
  template <class B> inline B REF unwrap() REF                                                                \
  { return MOVE(unwrap<TL::IdxOf<B, Ts>::val>()); }                                                           \
                                                                                                              \
  /**                                                                                                         \
   * returns the value of this Coproduct if its variant's index is idx. otherwise the result is undefined.    \
   *                                                                                                          \
   * \pre idx must be less than the number of variants of this Coproduct                                      \
   */                                                                                                         \
  template <unsigned idx>                                                                                     \
  inline TL::Get<idx, Ts> REF unwrap() REF {                                                                  \
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
  template <class B> inline Option<B REF> as() REF                                                            \
  { return is<B>() ? unwrap<B>() : Option<B REF>();  }                                                        \
                                                                                                              \
  /**                                                                                                         \
   * returns the value of this Coproduct if its variant's index is idx. otherwise an empty Option is returned.\
   *                                                                                                          \
   * \pre idx must be less than the number of variants of this Coproduct                                      \
   */                                                                                                         \
  template <unsigned idx>                                                                                     \
  inline Option<TL::Get<idx, Ts> REF> as() REF                                                                \
  { return is<idx>() ? unwrap<idx>() : Option<TL::Get<idx, Ts> REF>();  }                                     \

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

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
        self.apply([](auto const& x){ return std::hash<std::remove_const_t<std::remove_reference_t<decltype(x)>>>{}(x); }));
  }
};


template<class... As>
struct std::less<Lib::Coproduct<As...> >
{
  bool operator()(const Lib::Coproduct<As...>& lhs, const Lib::Coproduct<As...>& rhs)
  { return Lib::PolymorphicCoproductOrdering<std::less>{}(lhs,rhs); }
};

#endif // __LIB_COPRODUCT__H__

