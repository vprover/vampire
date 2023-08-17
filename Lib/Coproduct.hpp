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

#include <type_traits>
#define MACRO_EXPANSION true

#include "Debug/Assertion.hpp"
#include "Debug/Tracer.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Sort.hpp"
#include "Lib/TypeList.hpp"
#include "Lib/Option.hpp"
#include <memory>
#include <functional>

namespace Lib {

namespace TL = TypeList;

template<unsigned v>
struct Constant { static constexpr unsigned value = v; };

template <class... As> 
class Coproduct;

#define USE_SWITCH 0

#if USE_SWITCH 

template<unsigned maxExcl> struct SwitchImpl;

#define SWITCH_CONT_0
#define SWITCH_CONT_1  SWITCH_CONT_0  case 0:  return f(Constant<0>{});
#define SWITCH_CONT_2  SWITCH_CONT_1  case 1:  return f(Constant<1>{});
#define SWITCH_CONT_3  SWITCH_CONT_2  case 2:  return f(Constant<2>{});
#define SWITCH_CONT_4  SWITCH_CONT_3  case 3:  return f(Constant<3>{});
#define SWITCH_CONT_5  SWITCH_CONT_4  case 4:  return f(Constant<4>{});
#define SWITCH_CONT_6  SWITCH_CONT_5  case 5:  return f(Constant<5>{});
#define SWITCH_CONT_7  SWITCH_CONT_6  case 6:  return f(Constant<6>{});
#define SWITCH_CONT_8  SWITCH_CONT_7  case 7:  return f(Constant<7>{});
#define SWITCH_CONT_9  SWITCH_CONT_8  case 8:  return f(Constant<8>{});
#define SWITCH_CONT_10 SWITCH_CONT_9  case 9:  return f(Constant<9>{});
#define SWITCH_CONT_11 SWITCH_CONT_10 case 10: return f(Constant<10>{});
#define SWITCH_CONT_12 SWITCH_CONT_11 case 11: return f(Constant<11>{});
#define SWITCH_CONT_13 SWITCH_CONT_12 case 12: return f(Constant<12>{});
#define SWITCH_CONT_14 SWITCH_CONT_13 case 13: return f(Constant<13>{});
#define SWITCH_CONT_15 SWITCH_CONT_14 case 14: return f(Constant<14>{});
#define SWITCH_CONT_16 SWITCH_CONT_15 case 15: return f(Constant<15>{});

#define DECL_SWITCH_STRUCT(N)                                                             \
  template<>                                                                              \
  struct SwitchImpl<N> {                                                                  \
    template<class F>                                                                     \
    static auto apply(unsigned tag, F f) -> decltype(auto) {                              \
      if (tag < N) {                                                                      \
        switch (tag) {                                                                    \
          SWITCH_CONT_ ## N                                                               \
        }                                                                                 \
      }                                                                                   \
      ASSERTION_VIOLATION                                                                 \
    }                                                                                     \
  };                                                                                      \

DECL_SWITCH_STRUCT(1)
DECL_SWITCH_STRUCT(2)
DECL_SWITCH_STRUCT(3)
DECL_SWITCH_STRUCT(4)
DECL_SWITCH_STRUCT(5)
DECL_SWITCH_STRUCT(6)
DECL_SWITCH_STRUCT(7)
DECL_SWITCH_STRUCT(8)
DECL_SWITCH_STRUCT(9)
DECL_SWITCH_STRUCT(10)
DECL_SWITCH_STRUCT(11)
DECL_SWITCH_STRUCT(12)
DECL_SWITCH_STRUCT(13)
DECL_SWITCH_STRUCT(14)
DECL_SWITCH_STRUCT(15)
DECL_SWITCH_STRUCT(16)


template<unsigned N, class F> auto switchN(unsigned tag, F fun) -> decltype(auto)
{ return SwitchImpl<N>::apply(tag, std::move(fun)); }

#else // !USE_SWITCH

template<unsigned I, unsigned N> 
struct SwitchImpl
{
  static_assert(I < N, "out of bounds");
  template<class F>
  inline static auto apply(unsigned tag, F f) -> decltype(auto) {
    if (tag == I) {
      return f(Constant<I>{});
    }
    return SwitchImpl<I + 1, N>::apply(tag, f);
  }
};

template<unsigned N>
struct SwitchImpl<N, N + 1> {
  template<class F>
  inline static auto apply(unsigned tag, F f) -> decltype(auto) 
  { 
    ASS_EQ(tag, N)
    return f(Constant<N>{});
  }
};


template<unsigned N, class F> inline auto switchN(unsigned tag, F fun) -> decltype(auto)
{ return SwitchImpl<0, N>::apply(tag, fun); }

#endif 


constexpr unsigned neededBits(unsigned i)
{ return i <= 1       ? 0
       : (i & 1) == 1 ? neededBits(i + 1)
                      : 1 + neededBits(i >> 1); }

constexpr unsigned bitMask(unsigned i)
{ return ~(unsigned(-1) << neededBits(i)); }


template<class... As> 
class Coproduct;

/** This namespace constains helper classes and functions to implement the coproduct */
namespace CoproductImpl {

#define NEW_VARIADIC_UNION 1

#if NEW_VARIADIC_UNION

  template<class... Ts>
  struct MaxSize;

  template<> 
  struct MaxSize<> 
  { static constexpr unsigned value = 0; };

  template<class T, class... Ts> 
  struct MaxSize<T, Ts...> 
  { static constexpr unsigned value = std::max<unsigned>(sizeof(T), MaxSize<Ts...>::value); };


  struct MarkNotTrivial {
    struct Nothing {};

    struct CopyCons { CopyCons() {} CopyCons(CopyCons const&) {} };
    struct MoveCons { MoveCons() {} MoveCons(CopyCons const&) {} };

    struct Destr { ~Destr() {} };


  };

  // TODO update doc
  /** This class is an untagged union of all type arguments. It is defined inductively by template specialization. 
   * In a pseudo haskellish syntax the definition of the union can be thought of like this:
   * data VariadicUnion []      = bottom type
   * data VariadicUnion (a::as) = union {a, Coproduct as}
   */
  template <class... As> 
  struct VariadicUnion
  { 
    CLASS_NAME(VariadicUnion)
    using Ts = TL::List<As...>;
    using Bytes = char [MaxSize<As...>::value];

    Bytes _data;
    using M = MarkNotTrivial;
    template<template<class> class Pred, class Marker>
    using MarkNonTrivial = std::conditional_t<TL::All<Pred, Ts>::val, M::Nothing, Marker>;

    // MarkNonTrivial<is_trivially_copy_constructible, is_trivially_copy_constructible, M::CopyCons> _trivCopy;
    // MarkNonTrivial<is_trivially_copy_constructible, is_trivially_destructible      , M::Destr   > _trivDestruct;

    VariadicUnion() {}

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
    template<class B>                                                                     \
    B REF cast() REF                                                                      \
    {                                                                                     \
      static_assert(TL::Contains<B, TL::List<As...>>::val, "invalid cast");               \
      return (B REF) *this;                                                               \
    }                                                                                     \

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)

#undef REF_POLYMORPIHIC
  };

  // static_assert( std::is_trivially_copyable<VariadicUnion<int, int>>::value, "test 01");
  // static_assert(!std::is_trivially_copyable<std::vector<int>>::value, "test 02");
  // static_assert(!TL::All<is_trivially_copyable, TL::List<std::vector<int>, int>>::val, "test 03");
  // static_assert(!std::is_trivially_copyable<VariadicUnion<std::vector<int>, int>>::value, "test 04");
  //
  // static_assert( std::is_trivially_destructible<VariadicUnion<int, int>>::value, "test 01");
  // static_assert(!std::is_trivially_destructible<std::vector<int>>::value, "test 02");
  // static_assert(!TL::All<is_trivially_destructible, TL::List<std::vector<int>, int>>::val, "test 03");
  // static_assert(!std::is_trivially_destructible<VariadicUnion<std::vector<int>, int>>::value, "test 04");

#define MK_CONS(PREFIX, REF, MOVE)                                                        \
  template<class T>                                                                       \
  struct PREFIX ## Cons : public T {                                                      \
    PREFIX ## Cons() : T() {}                                                             \
    PREFIX ## Cons(PREFIX ## Cons REF other)                                              \
      : T()                                                                               \
    { *this = MOVE(other); }                                                              \
                                                                                          \
    PREFIX ## Cons& operator=(PREFIX ## Cons REF other)                                   \
    {                                                                                     \
      this->assignTag(other.tag());                                                       \
      this->switchN([&](auto N) {                                                         \
          using A = TL::Get<N.value, typename T::Ts>;                                     \
          ::new(&this->_content) A(MOVE(other._content.template cast<A>()));              \
      });                                                                                 \
      return *this;                                                                       \
    }                                                                                     \
  };                                                                                      \
  template<class T>                                                                       \
  struct PREFIX ## Assign : public T {                                                    \
    PREFIX ## Assign() : T() {}                                                           \
    PREFIX ## Assign& operator=(PREFIX ## Assign REF other)                               \
    {                                                                                     \
      this->assignTag(other.tag());                                                       \
      this->switchN([&](auto N) {                                                         \
          using A = TL::Get<N.value, typename T::Ts>;                                     \
          ::new(&this->_content) A(MOVE(other._content.template cast<A>()));              \
      });                                                                                 \
      return *this;                                                                       \
    }                                                                                     \
  };                                                                                      \

  MK_CONS(Copy, const&,          )
  MK_CONS(Move,     &&, std::move)

  template<class T>
  struct Destr : public T {
    Destr() : T() {}
    ~Destr()
    { 
      this->switchN([&](auto N) {
          using A = TL::Get<N.value, typename T::Ts>;
          this->_content.template cast<A>().~A();
      }); 
    }
  };


  template<class T, class F>
  struct CopyWith : public T {

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
    CopyWith(CopyWith REF other)                                                          \
      : T()                                                                               \
    { F{}(*this, MOVE(other)); }
  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
    CopyWith& operator=(CopyWith REF) = default;
  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  };

  template<class T, class F>
  struct DestructWith : public T {
    ~DestructWith() 
    { F{}((T&)*this); }
  };

  template<class... As>
  class Raw {

    template<class> friend struct CopyCons;
    template<class> friend struct CopyAssign;
    template<class> friend struct MoveCons;
    template<class> friend struct MoveAssign;
    template<class> friend struct Destr;

    template<class... Bs> friend class Lib::Coproduct;

    /** a type-level list of all types of this Coproduct */
    using Ts = TL::List<As...>;
    /** the number of alternatives */
    static constexpr unsigned size = TL::Size<Ts>::val;
    static_assert(size == 0 || size - 1 == ((size - 1) & bitMask(size)), "bug in function neededBits");

    unsigned _tag: neededBits(size);
    VariadicUnion<As...> _content;

    Raw() = default;

    unsigned tag() const { return _tag; }

    template<unsigned tag>
    void assignTag()
    { 
      static_assert(tag < size, "tag out of bounds");
      static_assert((tag & bitMask(size)) == tag, "unexpected lib author error");
      _tag = tag; 
    }

    void assignTag(unsigned tag)
    { 
      ASS_REP(tag < size, "tag out of bounds");
      ASS_REP((tag & bitMask(size)) == tag, "unexpected lib author error");
      _tag = tag; 
    }

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
    template<class F>                                                                     \
    auto switchN(F f) REF -> decltype(auto)                                               \
    { return Lib::switchN<size>(_tag, std::move(f)); }                                    \

FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  };

  template<class A>
  class Raw<A> {

    template<class> friend struct CopyCons;
    template<class> friend struct CopyAssign;
    template<class> friend struct MoveCons;
    template<class> friend struct MoveAssign;
    template<class> friend struct Destr;

    template<class... Bs> friend class Lib::Coproduct;

    /** a type-level list of all types of this Coproduct */
    using Ts = TL::List<A>;

    /** the number of alternatives */
    static constexpr unsigned size = TL::Size<Ts>::val;
    VariadicUnion<A> _content;

    Raw() = default;

    template<unsigned tag>
    void assignTag()
    { static_assert(tag == 0, "tag out of bounds"); }

    void assignTag(unsigned tag)
    { ASS_REP(tag == 0, "tag out of bounds"); }


#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
    template<class F>                                                                     \
    auto switchN(F f) REF -> decltype(auto)                                               \
    { return Lib::switchN<1>(0, std::move(f)); }                                          \

FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC


    constexpr unsigned tag() const { return 0; }
  };


  template<template<class> class OpPossible,template<class> class OpTrivial, 
           class Ts, template<class> class W, class A>
  using Wrap_ = 
    std::conditional_t<TL::All<OpTrivial , Ts>::val, A,
    std::conditional_t<TL::All<OpPossible, Ts>::val, W<A>,
                                                     A>>;


  template<class... As>
  using Raw2 = 
     Wrap_<is_copy_constructible          ,is_trivially_copy_constructible, TL::List<As...>, CopyCons,
     Wrap_<is_move_constructible          ,is_trivially_move_constructible, TL::List<As...>, MoveCons,
     // Wrap_<is_copy_assignable             ,is_trivially_copy_assignable   , TL::List<As...>, CopyAssign,
     // Wrap_<is_move_assignable             ,is_trivially_move_assignable   , TL::List<As...>, MoveAssign,
     Wrap_<is_destructible                ,is_trivially_destructible      , TL::List<As...>, Destr,
       Raw<As...>
      >>>;
  //MkCopy<MkDestr<Raw<As...>>>;



#else  // !NEW_VARIADIC_UNION

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
    ~VariadicUnion() {}
  };

  /** Inductive case of the inductive definition of VariadicUnion.  
   *
   * data VariadicUnion (a::as) = union {a, Coproduct as}
   */
  template <class A, class... As> union VariadicUnion<A, As...> {
    CLASS_NAME(VariadicUnion)
    using Ts = TL::List<A,As...>;

    A _head;
    VariadicUnion<As...> _tail;

    ~VariadicUnion() {}
    VariadicUnion() {}

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
    template<class B>                                                                     \
    B REF cast() REF                                                                      \
    {                                                                                     \
      static_assert(TL::Contains<B, TL::List<A, As...>>::val, "invalid cast");            \
      return (B REF)*this;                                                                \
    }                                                                                     \

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC


  }; // VariadicUnion


#endif // NEW_VARIADIC_UNION
} // namespace CoproductImpl



template<unsigned i, class A>
class Variant {
  A _self;
  template<class...>
  friend class Coproduct;
public:
  Variant(A a) : _self(move_if_value<A>(a)) {}
};

template<unsigned i, class A>
Variant<i, A> variant(A a) 
{ return Variant<i, A>(move_if_value<A>(a)); };




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
template <class... As> 
class Coproduct
{
  CoproductImpl::Raw2<As...> _inner;


  /** a type-level list of all types of this Coproduct */
  using Ts = TL::List<As...>;

  /** the number of alternatives */
  static constexpr unsigned size = TL::Size<Ts>::val;

  /** unsafe default constructor, content will be uninit */
  // TODO allow uninit constructor if all alternatives are uninit constructible
  Coproduct() {}

  inline unsigned tag() const { return _inner.tag(); }

public:
  CLASS_NAME(Coproduct)
public:

  /** Returns whether this coproduct is the variant idx */
  template<unsigned idx> bool is() const 
  {
    static_assert(idx < size, "out of bounds");
    return tag() == idx;
  }

  /** 
   * Returns whether this coproduct is the variant witht he given type. 
   * \pre is exactly one occurence of the type B in this Coproduct's types (As...).
   */
  template <class B> bool is() const 
  { return is<TL::IdxOf<B, Ts>::val>(); }

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
                                                                                          \
  /* Coproduct &operator=(Coproduct REF other) {                                          \
    this->~Coproduct();                                                                   \
    ::new(this) Coproduct(MOVE(other));                                                   \
    return *this;                                                                         \
  }  */                                                                                   \
                                                                                          \
  /**                                                                                     \
   * constructs a new Coproduct with the variant idx.                                     \
   * \pre B must occur exactly once in As...                                              \
   */                                                                                     \
  template<class B, std::enable_if_t<TL::Contains<B, Ts>::val, int> = 0>                  \
  explicit Coproduct(B REF b)                                                             \
    : Coproduct(variant<TL::IdxOf<B, Ts>::val>(MOVE(b)))                                  \
  { }                                                                                     \
                                                                                          \
   /**                                                                                    \
   * transforms all variants of this Coproduct to the same type and retuns the result     \
   *                                                                                      \
   * The arguments F... must all be function whichs argument type must match the type of the corresponding    \
   * variant of this Coproduct. The output types of the functions must all be the same type, which will be    \
   * the return type of this function.                                                    \
   */                                                                                     \
  template <class... F>                                                                   \
  inline auto match(F... fs) REF -> decltype(auto) {                                      \
    auto fs_ = std::tie(fs...);                                                           \
    return _inner.switchN([&](auto N) -> decltype(auto) {                                 \
        auto& f = get<N.value>(fs_);                                                      \
        return f(unwrap<N.value>());                                                      \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * transforms all variants of this Coproduct to the same type and retuns the result     \
   *                                                                                      \
   * This function works basically in the same way as match, but takes one polymorphic function object that   \
   * can transform any variant instead of multiple functions per variant.                 \
   */                                                                                     \
  template <class F>                                                                      \
  inline ResultOf<F, TL::Get<0, Ts> REF> apply(F f) REF {                                 \
    return _inner.switchN([&](auto N) -> decltype(auto) {                                 \
        return f(MOVE(unwrap<N.value>()));                                                \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  template <class F>                                                                      \
  inline ResultOf<F, TL::Get<0, Ts> REF, Constant<0>> applyWithIdx(F f) REF {             \
    return _inner.switchN([&](auto N) -> decltype(auto) {                                 \
        return f(MOVE(unwrap<N.value>()), N);                                             \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is of another type       \
   * the result is undefined.                                                             \
   *                                                                                      \
   * \pre B must occur exactly once in As...                                              \
   */                                                                                     \
  template <class B> inline B REF unwrap() REF                                            \
  { return MOVE(unwrap<TL::IdxOf<B, Ts>::val>()); }                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant's index is idx. otherwise the result is undefined.    \
   *                                                                                      \
   * \pre idx must be less than the number of variants of this Coproduct                  \
   */                                                                                     \
  template <unsigned idx>                                                                 \
  inline TL::Get<idx, Ts> REF unwrap() REF {                                              \
    static_assert(idx < size, "out of bounds");                                           \
    ASS_EQ(idx, tag());                                                                   \
    return MOVE(_inner._content.template cast<TL::Get<idx, Ts>>());                       \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is of another type       \
   * an empty Option is returned.                                                         \
   *                                                                                      \
   * \pre B must occur exactly once in As...                                              \
   */                                                                                     \
  template <class B> inline Option<B REF> as() REF                                        \
  { return as<TL::IdxOf<B, Ts>::val>(); }                                                 \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant's index is idx. otherwise an empty Option is returned.\
   *                                                                                      \
   * \pre idx must be less than the number of variants of this Coproduct                  \
   */                                                                                     \
  template <unsigned idx>                                                                 \
  inline Option<TL::Get<idx, Ts> REF> as() REF                                            \
  {                                                                                       \
    using B = TL::Get<idx, Ts>;                                                           \
    return is<idx>() ? Option<B REF>(MOVE(unwrap<idx>()))                                 \
                     : Option<B REF>();                                                   \
  }                                                                                       \

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  // TODO trivial one
  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs)
  {
    return lhs.tag() == rhs.tag() 
      && lhs._inner.switchN([&](auto N) {
          return lhs.unwrap<N.value>() == rhs.unwrap<N.value>();
      });
  }

  // TODO trivial one
  friend bool operator!=(const Coproduct &lhs, const Coproduct &rhs)
  { return !(lhs == rhs); }

  template <unsigned idx, class B>
  Coproduct(Variant<idx, B> value) 
  {
    static_assert(TL::Contains<B, Ts>::val, "not a variant of Coproduct");
    static_assert(idx < size, "variant index out of bounds");
    static_assert(std::is_same<B, TL::Get<idx, Ts>>::value, "illegal index for variant");

    Coproduct self;
    self._inner.template assignTag<idx>();
    ::new(&self._inner._content) B(std::move(value._self));
  }

  /**                                                                                     \
   * constructs a new Coproduct with the variant idx. The argument type must match 
   * `idx`th type of this * corpoduct's variants types (As...).
   */
  template <unsigned idx>
  static Coproduct variant(TL::Get<idx, Ts> value) 
  { return Coproduct(Variant<idx, TL::Get<idx, Ts>>(move_if_value<TL::Get<idx, Ts>>(value))); }

  friend std::ostream &operator<<(std::ostream &out, const Coproduct &self)
  { return self.apply([&](auto const& x)  -> std::ostream&
        { return out << "var" << self.tag() << "(" << x << ")"; }); }

  friend struct std::hash<Coproduct>;

  __attribute__((noinline))
  inline Lib::Comparison compare(Coproduct const& rhs) const
  { 
    auto& lhs = *this;
    return  lexCompare(DefaultComparator::compare(lhs.tag(), rhs.tag()),
        [&](){
          return lhs._inner.switchN([&](auto N){
              return DefaultComparator::compare(
                  lhs.template unwrap<N.value>(),
                  rhs.template unwrap<N.value>());
           });
        });
  }


  IMPL_COMPARISONS_FROM_COMPARE(Coproduct)

  unsigned defaultHash() const
  { return Lib::HashUtils::combine( std::hash<unsigned>{}(tag()), apply([](auto const& x){ return x.defaultHash(); })); }

  unsigned defaultHash2() const
  { return Lib::HashUtils::combine( std::hash<unsigned>{}(tag()), apply([](auto const& x){ return x.defaultHash2(); })); }

  inline Coproduct clone() const { return apply([](auto& x){ return Coproduct(x.clone()); }); }
}; // class Coproduct<As...> 



} // Lib

template<class... Ts> struct std::hash<Lib::Coproduct<Ts...>>
{
  size_t operator()(Lib::Coproduct<Ts...> const& self) const
  {
    return Lib::HashUtils::combine(
        std::hash<unsigned>{}(self.tag()),
        self.apply([](auto const& x){ return std::hash<std::remove_const_t<std::remove_reference_t<decltype(x)>>>{}(x); }));
  }
};


#endif // __LIB_COPRODUCT__H__

