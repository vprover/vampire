#ifndef SUBSAT_HPP
#define SUBSAT_HPP

#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <limits>
#include <new>

// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(!VDEBUG, "");
#else
static_assert(VDEBUG, "");
#endif

// TODO:
// Once this works, make a separate version 'matchsat',
// which keeps an array of matches as well.
// (see my notes on SAT+CSP)

namespace SMTSubsumption {

using std::uint32_t;

enum class Value : signed char {
  False = -1,
  Unknown = 0,
  True = 1,
};

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

  [[nodiscard]] constexpr uint32_t index() const noexcept
  {
    return m_index;
  }

  [[nodiscard]] static constexpr uint32_t max_index() noexcept
  {
    return (1u << 31) - 2;
  }

  [[nodiscard]] static constexpr Var invalid() noexcept
  {
    return Var{std::numeric_limits<uint32_t>::max()};
  }

  // [[nodiscard]] constexpr Lit operator~() const noexcept
  // {
  //   return Lit{*this, false};
  // }

  // [[nodiscard]] constexpr operator Lit() const noexcept
  // {
  //   return Lit{*this, true};
  // }
}; // Var

static_assert(Var::max_index() == static_cast<uint32_t>(INT32_MAX - 1), "unexpected max variable index");
static_assert(Var::max_index() < Var::invalid().index(), "valid variable indices overlap with invalid sentinel value");

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
  Lit() noexcept
  // : m_index{Lit::invalid().index()}
  {
  }

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

  [[nodiscard]] static constexpr Lit pos(Var var) noexcept
  {
    return Lit{var, true};
  }

  [[nodiscard]] static constexpr Lit neg(Var var) noexcept
  {
    return Lit{var, false};
  }

  [[nodiscard]] constexpr uint32_t index() const noexcept
  {
    return m_index;
  }

  [[nodiscard]] static constexpr uint32_t max_index() noexcept
  {
    static_assert(Var::max_index() < (std::numeric_limits<uint32_t>::max() - 1) / 2, "cannot represent all literals");
    return 2 * Var::max_index() + 1;
  }

  [[nodiscard]] static constexpr Lit invalid() noexcept
  {
    return Lit{std::numeric_limits<uint32_t>::max()};
  }

  [[nodiscard]] constexpr bool is_positive() const noexcept
  {
    return (m_index & 1) == 0;
  }

  [[nodiscard]] constexpr bool is_negative() const noexcept
  {
    return !is_positive();
  }

  [[nodiscard]] constexpr Lit operator~() const noexcept
  {
    return Lit{m_index ^ 1};
  }
}; // Lit

static_assert(Lit::max_index() < Lit::invalid().index(), "valid literal indices overlap with invalid sentinel value");

inline void* subsat_alloc(std::size_t size)
{
#ifdef SUBSAT_STANDALONE
  void* p = std::malloc(size);
#else
  void* p = ALLOC_UNKNOWN(size, "subsat");
#endif
  if (!p && size > 0) {
    throw std::bad_alloc();
  }
  return p;
}

inline void subsat_dealloc(void* p)
{
#ifdef SUBSAT_STANDALONE
  std::free(p);
#else
  DEALLOC_UNKNOWN(p, "subsat");
#endif
}






class Clause final {
  uint32_t m_size;   // number of literals
  Lit m_literals[2]; // actual size is m_size, but C++ does not officially support flexible array members (as opposed to C)

public:
  using iterator = Lit const*;

  [[nodiscard]] iterator begin() const noexcept
  {
    return &m_literals[0];
  }

  [[nodiscard]] iterator end() const noexcept
  {
    return begin() + m_size;
  }

  /// Number of bytes required by a clause containing 'size' literals.
  static size_t bytes(uint32_t size) noexcept
  {
    size_t const contained_literals = std::extent_v<decltype(m_literals)>;
    size_t const additional_literals = (size >= contained_literals) ? (size - contained_literals) : 0;
    size_t const total_bytes = sizeof(Clause) + sizeof(Lit) * additional_literals;
    return total_bytes;
  }

  /// Allocate a clause with enough space for 'size' literals.
  static Clause* create(uint32_t size)
  {
    void* p = subsat_alloc(bytes(size));
    return new (p) Clause{size};
  }

  // static void* operator new(size_t, uint32_t num_literals)
  // {
  //   size_t const contained_literals = std::extent_v<decltype(m_literals)>;
  //   size_t const additional_literals = std::max(0, static_cast<size_t>(num_literals) - contained_literals);
  //   size_t const total_bytes = sizeof Clause + sizeof Lit * additional_literals;
  //   return ::operator new(total_bytes);
  // }

private:
  // NOTE: do not use this constructor directly
  // because it does not allocate enough memory for the literals
  Clause(uint32_t size) noexcept
      : m_size{size}
  {
  }

  // cannot copy/move because of flexible array member
  Clause(Clause&) = delete;
  Clause(Clause&&) = delete;
  Clause& operator=(Clause&) = delete;
  Clause& operator=(Clause&&) = delete;
}; // Clause



class Solver
{
  int x;
}; // Solver



} // namespace SMTSubsumption

#endif /* !SUBSAT_HPP */
