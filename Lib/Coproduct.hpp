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

#define USE_SWITCH 1

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
    static auto apply(unsigned tag, F f) -> decltype(auto) {                       \
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

} // namespace CoproductImpl



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

  /** a type-level list of all types of this Coproduct */
  using Ts = TL::List<A, As...>;

  /** the number of alternatives */
  static constexpr unsigned size = TL::Size<Ts>::val;
  static_assert(size == 0 || size - 1 == ((size - 1) & bitMask(size)), "bug in function neededBits");


  /* _tag specifies which of the types in `A, As...` is actually stored in the field _content */
  unsigned _tag: neededBits(size);
  CoproductImpl::VariadicUnion<A, As...> _content;

  using Self = Coproduct<A, As...>;
  using Content = decltype(_content);

  /** unsafe default constructor, content will be uninit */
#if VDEBUG
  Coproduct() : _tag(-1) {}
#else //!VDEBUG
  Coproduct() {}
#endif

public:
  CLASS_NAME(Coproduct)
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

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
                                                                                          \
  Coproduct(Coproduct REF other) : _tag(other._tag) {                                     \
    ASS_REP(other._tag < size, other._tag);                                               \
    switchN<size>(other._tag, [&](auto N) {                                               \
        ::new(&_content) TL::Get<N.value, Ts>(MOVE(other).template unwrap<N.value>());    \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * constructs a new Coproduct with the variant idx.                                     \
   * \pre B must occur exactly once in A,As...                                            \
   */                                                                                     \
  template<class B>                                                                       \
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
    ASS_REP(_tag < size, _tag);                                                           \
    auto fs_ = std::tie(fs...);                                                           \
    return switchN<size>(_tag, [&](auto N) -> decltype(auto) {                            \
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
  inline ResultOf<F, A REF> apply(F f) REF {                                              \
    ASS_REP(_tag < size, _tag);                                                           \
    using R = ResultOf<F, A REF>;                                                         \
    return applyWithIdx([&](auto REF a, auto _idx) -> R { return f(MOVE(a)); });          \
  }                                                                                       \
                                                                                          \
  template <class F>                                                                      \
  inline ResultOf<F, A REF, Constant<0>> applyWithIdx(F f) REF {                          \
    return switchN<size>(_tag, [&](auto N) -> decltype(auto) {                            \
        return f(unwrap<N.value>(), N);                                                   \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  Coproduct &operator=(Coproduct REF other) {                                             \
    this->~Coproduct();                                                                   \
    ::new(this) Coproduct(MOVE(other));                                                   \
    return *this;                                                                         \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is of another type       \
   * the result is undefined.                                                             \
   *                                                                                      \
   * \pre B must occur exactly once in A,As...                                            \
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
    ASS_EQ(idx, _tag);                                                                    \
    return MOVE(_content).template cast<TL::Get<idx, Ts>>();                              \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is of another type       \
   * an empty Option is returned.                                                         \
   *                                                                                      \
   * \pre B must occur exactly once in A,As...                                            \
   */                                                                                     \
  template <class B> inline Option<B REF> as() REF                                        \
  { return is<B>() ? Option<B REF>(unwrap<B>()) : Option<B REF>();  }                     \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant's index is idx. otherwise an empty Option is returned.\
   *                                                                                      \
   * \pre idx must be less than the number of variants of this Coproduct                  \
   */                                                                                     \
  template <unsigned idx>                                                                 \
  inline Option<TL::Get<idx, Ts> REF> as() REF                                            \
  { return is<idx>() ? Option<TL::Get<idx, Ts> REF>(unwrap<idx>()) : Option<TL::Get<idx, Ts> REF>();  }                                     \

  FOR_REF_QUALIFIER(REF_POLYMORPIHIC)
#undef REF_POLYMORPIHIC

  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs)
  {
    return lhs._tag == rhs._tag 
      && switchN<size>(lhs._tag, [&](auto N) {
          return lhs.unwrap<N.value>() == rhs.unwrap<N.value>();
      });
  }

  friend bool operator!=(const Coproduct &lhs, const Coproduct &rhs)
  { return !(lhs == rhs); }

  ~Coproduct() 
  { 
    switchN<size>(_tag, [&](auto N) {
        using T = TL::Get<N.value, Ts>;
        _content.template cast<T>().~T();
    });
  }
                                                                                          \
  /**                                                                                     \
   * constructs a new Coproduct with the variant idx. The argument type must match 
   * `idx`th type of this * corpoduct's variants types (A,As...).
   */
  template <unsigned idx>
  static Coproduct variant(TL::Get<idx, Ts> value) 
  {
    static_assert(idx < size, "out of bounds");
    static_assert((idx & bitMask(size)) == idx, "out of bounds");
    using T = TL::Get<idx, Ts>;
    Coproduct self;
    self._tag = idx & bitMask(size); // <- bit mask to get the compiler to not warn about potential truncation of unsigned to bitfield value. This does not affect the value of the assignment, as we have a static_assert(idx < size) before
    ::new(&self._content) T(std::move(value));
    return self;
  }

  friend std::ostream &operator<<(std::ostream &out, const Coproduct &self)
  { return self.apply([&](auto const& x)  -> std::ostream&
        { return out << "var" << self._tag << "(" << x << ")"; }); }

  friend struct std::hash<Coproduct>;

  inline Lib::Comparison compare(Coproduct const& rhs) const
  { 
    auto& lhs = *this;
    return  lexCompare(DefaultComparator::compare(lhs._tag, rhs._tag),
        [&](){
          return switchN<size>(lhs._tag, [&](auto N){
              return DefaultComparator::compare(
                  lhs.template unwrap<N.value>(),
                  rhs.template unwrap<N.value>());
           });
        });
  }


  IMPL_COMPARISONS_FROM_COMPARE(Coproduct)

  unsigned defaultHash() const
  { return Lib::HashUtils::combine( std::hash<unsigned>{}(_tag), apply([](auto const& x){ return x.defaultHash(); })); }

  unsigned defaultHash2() const
  { return Lib::HashUtils::combine( std::hash<unsigned>{}(_tag), apply([](auto const& x){ return x.defaultHash2(); })); }

  inline Coproduct clone() const { return apply([](auto& x){ return Coproduct(x.clone()); }); }
}; // class Coproduct<A, As...> 



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


#endif // __LIB_COPRODUCT__H__

