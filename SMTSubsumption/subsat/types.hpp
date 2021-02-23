#ifndef TYPES_HPP
#define TYPES_HPP

#include <cassert>
#include <cstdint>
#include <limits>
#include <ostream>

#include "./vector_map.hpp"

namespace subsat {

#if __cplusplus >= 201703L
#define NODISCARD [[nodiscard]]
#else
#define NODISCARD
#endif

using std::uint8_t;
using std::uint32_t;


/// Value of a boolean variable/literal.
enum class Value : signed char {
  False = -1,
  Unassigned = 0,
  True = 1,
};

static Value operator~(Value v) {
  return static_cast<Value>(-static_cast<signed char>(v));
}

/*
static std::ostream& operator<<(std::ostream& os, Value v)
{
  switch (v) {
    case Value::False:
      os << "false";
      break;
    case Value::Unassigned:
      os << "unassigned";
      break;
    case Value::True:
      os << "true";
      break;
    // default:
    //   os << "illegal(" << static_cast<std::underlying_type_t<Value>>(v) << ")";
    //   break;
  }
  return os;
}
*/


/// Solver result.
enum class Result : int {
  Sat = 10,
  Unsat = 20,
};

static std::ostream& operator<<(std::ostream& os, Result r)
{
  switch (r) {
    case Result::Sat:
      os << "satisfiable";
      break;
    case Result::Unsat:
      os << "unsatisfiable";
      break;
    // default:
    //   os << "illegal(" << static_cast<std::underlying_type_t<Result>>(r) << ")";
    //   break;
  }
  return os;
}


class Lit;

/// Boolean variable represented by its integer index.
/// Use consecutive indices starting at 0.
class Var final {
  uint32_t m_index;

public:
  explicit constexpr Var(uint32_t index) noexcept
      : m_index{index}
  {
    // assert(m_index <= Var::max_index());  // TODO: how to assert in constexpr constructor?
  }

  NODISCARD constexpr uint32_t index() const noexcept
  {
    return m_index;
  }

  NODISCARD static constexpr uint32_t max_index() noexcept
  {
    return (1u << 31) - 2;
  }

  NODISCARD static constexpr Var invalid() noexcept
  {
    return Var{std::numeric_limits<uint32_t>::max()};
  }

  NODISCARD constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  NODISCARD constexpr Lit operator~() const noexcept;
  NODISCARD constexpr operator Lit() const noexcept;
}; // Var

static_assert(Var::max_index() == static_cast<uint32_t>(INT32_MAX - 1), "unexpected max variable index");
static_assert(Var::max_index() < Var::invalid().index(), "valid variable indices overlap with invalid sentinel value");
static_assert(!Var::invalid().is_valid(), "");
static_assert(Var{Var::max_index()}.is_valid(), "");
// static_assert(std::is_trivially_constructible<Var>::value, "Var should be trivially constructible so we can allocate vectors without initialization");  // TODO: do we really need this for VMTF? maybe we need to initialize there anyway (then a reserve+push_back loop would do it.)
// static_assert(std::is_trivially_default_constructible<Var>::value, "Var should be trivially constructible so we can allocate vectors without initialization");  // TODO: do we really need this for VMTF? maybe we need to initialize there anyway (then a reserve+push_back loop would do it.)
// static_assert(std::is_trivially_constructible_v<Var>, "Var should be trivially constructible so we can allocate vectors without initialization");  // TODO: do we really need this for VMTF? maybe we need to initialize there anyway (then a reserve+push_back loop would do it.)
static_assert(std::is_trivially_destructible<Var>::value, "");

NODISCARD static constexpr bool operator==(Var lhs, Var rhs) noexcept
{
  return lhs.index() == rhs.index();
}

NODISCARD static constexpr bool operator!=(Var lhs, Var rhs) noexcept
{
  return !operator==(lhs, rhs);
}

NODISCARD static constexpr bool operator<(Var lhs, Var rhs) noexcept
{
  return lhs.index() < rhs.index();
}

static std::ostream& operator<<(std::ostream& os, Var var)
{
  if (var.is_valid()) {
    os << var.index();
  } else {
    os << "-";
  }
  return os;
}


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
  uint32_t m_index;

private:
  friend class Clause;
  /// Uninitialized value (for clause constructor)
  Lit() noexcept = default;

  explicit constexpr Lit(uint32_t index) noexcept
      : m_index{index}
  {
    // assert(m_index <= Lit::max_index()); // TODO: how to assert in constexpr constructor?
  }

public:
  explicit constexpr Lit(Var var, bool positive) noexcept
      : Lit{2 * var.index() + static_cast<uint32_t>(!positive)}
  {
  }

  NODISCARD static constexpr Lit from_index(uint32_t index) noexcept
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

  NODISCARD constexpr uint32_t index() const noexcept
  {
    return m_index;
  }

  NODISCARD static constexpr uint32_t max_index() noexcept
  {
    static_assert(Var::max_index() < (std::numeric_limits<uint32_t>::max() - 1) / 2, "cannot represent all literals");
    return 2 * Var::max_index() + 1;
  }

  NODISCARD static constexpr Lit invalid() noexcept
  {
    return Lit{std::numeric_limits<uint32_t>::max()};
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
}; // Lit

static_assert(Lit::max_index() < Lit::invalid().index(), "valid literal indices overlap with invalid sentinel value");
static_assert(!Lit::invalid().is_valid(), "");
static_assert(Lit{Var{Var::max_index()}, true}.is_valid(), "");
static_assert(Lit{Var{Var::max_index()}, false}.is_valid(), "");
// static_assert(std::is_trivially_constructible<Lit>::value, "");
static_assert(std::is_trivially_destructible<Lit>::value, "");



NODISCARD static constexpr bool operator==(Lit lhs, Lit rhs) noexcept
{
  return lhs.index() == rhs.index();
}

NODISCARD static constexpr bool operator!=(Lit lhs, Lit rhs) noexcept
{
  return !operator==(lhs, rhs);
}

static std::ostream& operator<<(std::ostream& os, Lit lit)
{
  if (lit.is_valid()) {
    if (lit.is_negative()) {
      os << '~';
    }
    os << lit.var();
  } else {
    os << "-";
  }
  return os;
}


NODISCARD constexpr Lit Var::operator~() const noexcept
{
  return Lit{*this, false};
}

NODISCARD constexpr Var::operator Lit() const noexcept
{
  return Lit{*this, true};
}

template <> struct DefaultIndex<Var> {
  using type = IndexMember<Var>;
};

template <> struct DefaultIndex<Lit> {
  using type = IndexMember<Lit>;
};


} // namespace subsat

#endif /* !TYPES_HPP */
