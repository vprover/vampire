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

#include "Debug/Assertion.hpp"
#include "Lib/Hash.hpp"
#include "Lib/Comparison.hpp"
#include "Lib/Reflection.hpp"
#include "Lib/Sort.hpp"
#include "Lib/TypeList.hpp"
#include "Lib/Option.hpp"
#include <functional>
#include <type_traits>
#include <tuple>
#include <variant>
#include <vector>

namespace Lib {

namespace TL = TypeList;

/* calls f(Constant<tag>{}) for a runtime I <= tag <= N; compiles to a jump table or branches */
template<unsigned I, unsigned N>
struct SwitchImpl
{
  static_assert(I < N, "out of bounds");
  template<class F>
  inline static ResultOf<F, Constant<0>> apply(unsigned tag, F f) {
    if (tag == I) {
      return f(Constant<I>{});
    }
    return SwitchImpl<I + 1, N>::apply(tag, std::move(f));
  }
};

template<unsigned N>
struct SwitchImpl<N, N> {
  template<class F>
  inline static ResultOf<F, Constant<0>> apply(unsigned tag, F f)
  {
    ASS_EQ(tag, N)
    return f(Constant<N>{});
  }
};

/**
 * The actual Coproduct class.
 * A coproduct, also called Sum type, is a union of types, tagged with indices. It can be constructed with
 * either of the type/index pairs, and in this implementation the index can be left away if all types in this
 * coproduct are distinct.
 *
 * Thin wrapper around std::variant. Prefer std::variant in new code.
 *
 * \see UnitTests/tCoproduct.cpp for usage
 */
template <class... As>
class Coproduct
{
  std::variant<As...> _inner;

  /** a type-level list of all types of this Coproduct */
  using Ts = TL::List<As...>;

  /** the number of alternatives */
  static constexpr unsigned size = sizeof...(As);

  /** calls f(Constant<tag()>{}) */
  template<class F>
  ResultOf<F, Constant<0>> switchN(F f) const
  { return SwitchImpl<0, size - 1>::apply(tag(), std::move(f)); }

  /** constructs the alternative idx in place */
  template<size_t idx, class... Args>
  explicit Coproduct(std::in_place_index_t<idx> i, Args&&... args)
    : _inner(i, std::forward<Args>(args)...) {}

public:

  inline unsigned tag() const
  {
    // also excludes valueless_by_exception(); in release builds this lets the compiler
    // drop the bounds check on the last alternative when dispatching
    ALWAYS(_inner.index() < size)
    return _inner.index();
  }

  /** Returns whether this coproduct is the variant idx */
  template<unsigned idx> bool is() const
  {
    static_assert(idx < size, "out of bounds");
    return tag() == idx;
  }

  /**
   * Returns whether this coproduct is the variant with he given type.
   * \pre is exactly one occurrence of the type B in this Coproduct's types (As...).
   */
  template <class B> bool is() const
  { return is<TL::IdxOf<B, Ts>::val>(); }

  /**
   * constructs a new Coproduct with the variant idx.
   * \pre B must occur exactly once in As...
   */
  template<class B, std::enable_if_t<TL::Contains<B, Ts>::val, int> = 0>
  explicit Coproduct(B b)
    : Coproduct(std::in_place_index<TL::IdxOf<B, Ts>::val>, move_if_value<B>(b))
  { }

#define REF_POLYMORPIHIC(REF, MOVE)                                                       \
                                                                                          \
   /**                                                                                    \
   * transforms all variants of this Coproduct to the same type and returns the result    \
   *                                                                                      \
   * The arguments F... must all be function whose argument type must match the type of   \
   * the corresponding * variant of this Coproduct. The output types of the functions must\
   * all be the same type, which will be the return type of this function.                \
   */                                                                                     \
  template <class... F>                                                                   \
  inline ResultOf<TL::Get<0, TL::List<F...>>, TL::Get<0, Ts> REF> match(F... fs) REF {    \
    auto fs_ = std::tie(fs...);                                                           \
    return switchN([&](auto N) -> decltype(auto) {                                        \
        auto& f = std::get<N.value>(fs_);                                                 \
        return f(unwrap<N.value>());                                                      \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * transforms all variants of this Coproduct to the same type and returns the result    \
   *                                                                                      \
   * This function works basically in the same way as match, but takes one polymorphic    \
   * function object that can transform any variant instead of multiple functions per     \
   * variant.                                                                             \
   */                                                                                     \
  template <class F>                                                                      \
  inline auto apply(F f) REF -> decltype(auto) {                                          \
    return switchN([&](auto N) -> decltype(auto) {                                        \
        return f(MOVE(unwrap<N.value>()));                                                \
    });                                                                                   \
  }                                                                                       \
  /**                                                                                     \
   * Like `apply` but not expecting that the function F will return the same type for any \
   * variant but instead `applyCo` returns a coproduct itself.                            \
   */                                                                                     \
  template <class F>                                                                      \
  inline auto applyCo(F f) REF -> decltype(auto) {                                        \
    using Out = Coproduct<std::invoke_result_t<F, As REF>...>;                            \
    return switchN([&](auto N) -> decltype(auto) {                                        \
        return Out::template variant<N.value>(f(MOVE(unwrap<N.value>())));               \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  template <class F>                                                                      \
  auto applyWithIdx(F f) REF -> decltype(auto) {                                          \
    return switchN([&](auto N) -> decltype(auto) {                                        \
        return f(MOVE(unwrap<N.value>()), N);                                             \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * Like `match` but not expecting that the function F will return the same type for any \
   * variant but instead `map` returns a coproduct itself.                                \
   */                                                                                     \
  template <class... F>                                                                   \
  auto map(F... fs) REF {                                                                 \
    auto fs_ = std::tie(fs...);                                                           \
    using Out = Coproduct<std::invoke_result_t<F, As>...>;                                \
    return switchN([&](auto N) -> decltype(auto) {                                        \
        auto& f = std::get<N.value>(fs_);                                                 \
        return Out::template variant<N.value>(f(unwrap<N.value>()));                      \
    });                                                                                   \
  }                                                                                       \
                                                                                          \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is   \
   * of another type the result is undefined.                                             \
   *                                                                                      \
   * \pre B must occur exactly once in As...                                              \
   */                                                                                     \
  template <class B> inline B REF unwrap() REF                                            \
  { return MOVE(unwrap<TL::IdxOf<B, Ts>::val>()); }                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant's index is idx. otherwise the     \
   * result is undefined.                                                                 \
   *                                                                                      \
   * \pre idx must be less than the number of variants of this Coproduct                  \
   */                                                                                     \
  template <unsigned idx>                                                                 \
  inline TL::Get<idx, Ts> REF unwrap() REF {                                              \
    static_assert(idx < size, "out of bounds");                                           \
    ASS_EQ(idx, tag());                                                                   \
    /* tells the compiler get_if cannot fail, so there is no runtime check */             \
    ALWAYS(_inner.index() == idx)                                                         \
    return MOVE(*std::get_if<idx>(&_inner));                                              \
  }                                                                                       \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant is of type B. If ifs variant is   \
   * of another type                                                                      \
   * an empty Option is returned.                                                         \
   *                                                                                      \
   * \pre B must occur exactly once in As...                                              \
   */                                                                                     \
  template <class B> inline Option<B REF> as() REF                                        \
  { return as<TL::IdxOf<B, Ts>::val>(); }                                                 \
                                                                                          \
  /**                                                                                     \
   * returns the value of this Coproduct if its variant's index is idx. otherwise an      \
   * empty Option is returned.                                                            \
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
  // (C++20 derives operator!= from this)
  friend bool operator==(const Coproduct &lhs, const Coproduct &rhs)
  {
    return lhs.tag() == rhs.tag()
      && lhs.applyWithIdx([&](auto& lhs, auto N) -> bool {
          return lhs == rhs.template unwrap<N.value>();
      });
  }

  /**
   * constructs a new Coproduct with the variant idx. The argument type must match
   * `idx`th type of this * corpoduct's variants types (As...).
   */
  template <unsigned idx>
  static Coproduct variant(TL::Get<idx, Ts> value)
  { return Coproduct(std::in_place_index<idx>, move_if_value<TL::Get<idx, Ts>>(value)); }

  friend std::ostream &operator<<(std::ostream &out, const Coproduct &self)
  { return self.apply([&](auto const& x)  -> std::ostream&
        { return out << "var" << self.tag() << "(" << x << ")"; }); }

  friend struct std::hash<Coproduct>;

  inline Lib::Comparison compare(Coproduct const& rhs) const
  {
    auto& lhs = *this;
    return  lexCompare(DefaultComparator::compare(lhs.tag(), rhs.tag()),
        [&](){
          return lhs.switchN([&](auto N){
              return DefaultComparator::compare(
                  lhs.template unwrap<N.value>(),
                  rhs.template unwrap<N.value>());
           });
        });
  }


  IMPL_COMPARISONS_FROM_COMPARE(Coproduct)

  inline Coproduct clone() const { return apply([](auto& x){ return Coproduct(x.clone()); }); }
}; // class Coproduct<As...>

static_assert( std::is_trivially_copyable<Coproduct<int, int>>::value, "trivially copyable alternatives must give a trivially copyable Coproduct");
static_assert(!std::is_trivially_copyable<Coproduct<std::vector<int>, int>>::value, "non-trivially copyable alternatives must not");
static_assert( std::is_trivially_destructible<Coproduct<int, int>>::value, "trivially destructible alternatives must give a trivially destructible Coproduct");
static_assert(!std::is_trivially_destructible<Coproduct<std::vector<int>, int>>::value, "non-trivially destructible alternatives must not");

// Combine the tag with the active alternative's hash, one functor per alternative.
template<class... ElementHashes>
struct CoproductHash {
  template<class... As>
  static unsigned hash(Coproduct<As...> const& c)
  {
    static_assert(sizeof...(ElementHashes) == sizeof...(As),
      "CoproductHash takes one hash functor per alternative");
    return HashUtils::combine(std::hash<unsigned>{}(c.tag()),
      c.match([](As const& x) -> unsigned { return ElementHashes::hash(x); }...));
  }
};

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
