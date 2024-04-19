/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef TYPES_HPP
#define TYPES_HPP

#include <cassert>
#include <cstdint>
#include <limits>
#include <ostream>
#include <set>
#include <map>

#include "./subsat_config.hpp"
#include "./vector_map.hpp"

#if !SUBSAT_STANDALONE
#include "Lib/STLAllocator.hpp"
#endif

namespace subsat {

#if __cplusplus >= 201703L
#define NODISCARD [[nodiscard]]
#else
#define NODISCARD
#endif

using std::uint8_t;
using std::uint32_t;

#if SUBSAT_STANDALONE
template <typename T>
using allocator_type = ::std::allocator<T>;
#else
template <typename T>
using allocator_type = ::Lib::STLAllocator<T>;
#endif

using string = std::basic_string<char, std::char_traits<char>, allocator_type<char>>;

template <typename T>
using vector = std::vector<T, allocator_type<T>>;

template <typename K, typename T>
using vector_map = subsat::vector_map_t<K, T, allocator_type<T>>;

#ifndef NDEBUG
  // Note: std::set and std::map are slow, so use them only in debug mode!
  template <typename Key, typename Compare = std::less<Key>>
  using set = typename ::std::set<Key, Compare, allocator_type<Key>>;
  template <typename Key, typename T, typename Compare = std::less<Key>>
  using map = typename ::std::map<Key, T, Compare, allocator_type<std::pair<Key const, T>>>;
#endif


class Lit;
class Solver;



/// Value of a boolean variable/literal.
enum class Value : signed char {
  False = -1,
  Unassigned = 0,
  True = 1,
};

constexpr Value operator~(Value v) {
  return static_cast<Value>(-static_cast<signed char>(v));
}

std::ostream& operator<<(std::ostream& os, Value v);



/// Solver result.
enum class Result : int {
  Unknown = 0,
  Sat = 10,
  Unsat = 20,
};

std::ostream& operator<<(std::ostream& os, Result r);



/// Boolean variable represented by its integer index.
/// Use consecutive indices starting at 0.
class Var final {
public:
  using index_type = std::uint32_t;

  explicit constexpr Var(index_type index) noexcept
      : m_index{index}
  {
    // assert(m_index <= Var::max_index());  // TODO: how to assert in constexpr constructor?
  }

  NODISCARD constexpr index_type index() const noexcept
  {
    return m_index;
  }

  NODISCARD static constexpr index_type max_index() noexcept
  {
    return (1u << 31) - 2;
  }

  NODISCARD static constexpr Var invalid() noexcept
  {
    return Var{std::numeric_limits<index_type>::max()};
  }

  NODISCARD constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  NODISCARD constexpr Lit operator~() const noexcept;

private:
  index_type m_index;
}; // Var

static_assert(Var::max_index() == static_cast<uint32_t>(INT32_MAX - 1), "unexpected max variable index");
static_assert(Var::max_index() < Var::invalid().index(), "valid variable indices overlap with invalid sentinel value");
static_assert(!Var::invalid().is_valid(), "");
static_assert(Var{Var::max_index()}.is_valid(), "");
static_assert(std::is_nothrow_copy_constructible<Var>::value, "");
static_assert(std::is_nothrow_copy_assignable<Var>::value, "");
static_assert(std::is_nothrow_move_constructible<Var>::value, "");
static_assert(std::is_nothrow_move_assignable<Var>::value, "");
static_assert(std::is_trivially_destructible<Var>::value, "");

NODISCARD static constexpr bool operator==(Var lhs, Var rhs) noexcept
{
  return lhs.index() == rhs.index();
}

NODISCARD static constexpr bool operator!=(Var lhs, Var rhs) noexcept
{
  return !operator==(lhs, rhs);
}

#ifndef NDEBUG
// for std::set<Var> in debug assertions
NODISCARD static constexpr bool operator<(Var lhs, Var rhs) noexcept
{
  return lhs.index() < rhs.index();
}
#endif

std::ostream& operator<<(std::ostream& os, Var var);



/// Boolean literals represented by integer index.
/// The least significant bit indicates the sign.
///
/// Mapping from variable indices to literal indices:
///    Lit{0} ... 0
///   ~Lit{0} ... 1
///    Lit{1} ... 2
///   ~Lit{1} ... 3
///      :
///      :
class Lit final {
public:
  using index_type = Var::index_type;

private:
  friend class Constraint;
  /// Uninitialized value (for constraint constructor)
  Lit() noexcept = default;

  explicit constexpr Lit(index_type index) noexcept
      : m_index{index}
  {
    // assert(m_index <= Lit::max_index()); // TODO: how to assert in constexpr constructor?
  }

public:
  /// Construct literal from variable and polarity.
  /// Enables implicit conversion from variables to positive literals.
  constexpr Lit(Var var, bool positive = true) noexcept
      : Lit{2 * var.index() + static_cast<index_type>(!positive)}
  {
  }

  NODISCARD static constexpr Lit from_index(index_type index) noexcept
  {
#if __cplusplus >= 201703L
    assert(index <= Lit::max_index());
    return Lit{index};
#else
    // return assert(index <= Lit::max_index()), Lit{index};
    return Lit{index};
#endif
  }

  NODISCARD static constexpr Lit pos(Var var) noexcept
  {
    return Lit{var, true};
  }

  NODISCARD static constexpr Lit neg(Var var) noexcept
  {
    return Lit{var, false};
  }

  NODISCARD constexpr index_type index() const noexcept
  {
    return m_index;
  }

  NODISCARD static constexpr index_type max_index() noexcept
  {
    static_assert(Var::max_index() < (std::numeric_limits<index_type>::max() - 1) / 2, "cannot represent all literals");
    return 2 * Var::max_index() + 1;
  }

  NODISCARD static constexpr Lit invalid() noexcept
  {
    return Lit{std::numeric_limits<index_type>::max()};
  }

  NODISCARD constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  NODISCARD constexpr bool is_positive() const noexcept
  {
    return (m_index & 1) == 0;
  }

  NODISCARD constexpr bool is_negative() const noexcept
  {
    return !is_positive();
  }

  NODISCARD constexpr Lit operator~() const noexcept
  {
    return Lit{m_index ^ 1};
  }

  NODISCARD constexpr Var var() const noexcept
  {
    return Var{m_index / 2};
  }

private:
  index_type m_index;
}; // Lit

static_assert(Lit::max_index() < Lit::invalid().index(), "valid literal indices overlap with invalid sentinel value");
static_assert(!Lit::invalid().is_valid(), "");
static_assert(Lit{Var{0}, true}.index() == 0, "");
static_assert(Lit{Var{0}, false}.index() == 1, "");
static_assert(Lit{Var{Var::max_index()}, true}.is_valid(), "");
static_assert(Lit{Var{Var::max_index()}, false}.is_valid(), "");
// static_assert(std::is_trivially_constructible<Lit>::value, "");
static_assert(std::is_nothrow_copy_constructible<Lit>::value, "");
static_assert(std::is_nothrow_copy_assignable<Lit>::value, "");
static_assert(std::is_nothrow_move_constructible<Lit>::value, "");
static_assert(std::is_nothrow_move_assignable<Lit>::value, "");
static_assert(std::is_trivially_destructible<Lit>::value, "");

NODISCARD static constexpr bool operator==(Lit lhs, Lit rhs) noexcept
{
  return lhs.index() == rhs.index();
}

NODISCARD static constexpr bool operator!=(Lit lhs, Lit rhs) noexcept
{
  return !operator==(lhs, rhs);
}

#ifndef NDEBUG
// for std::set<Lit> in debug assertions
NODISCARD static constexpr bool operator<(Lit lhs, Lit rhs) noexcept
{
  return lhs.index() < rhs.index();
}
#endif

std::ostream& operator<<(std::ostream& os, Lit lit);



NODISCARD constexpr Lit Var::operator~() const noexcept
{
  return Lit{*this, false};
}



template <> struct DefaultIndex<Var> {
  using type = IndexMember<Var>;
};

template <> struct DefaultIndex<Lit> {
  using type = IndexMember<Lit>;
};



} // namespace subsat

#endif /* !TYPES_HPP */
