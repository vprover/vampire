#ifndef CLAUSE_HPP
#define CLAUSE_HPP

#include <iostream>
#include <type_traits>
#include <vector>

#include "./types.hpp"

namespace SMTSubsumption {


class Clause final
{
public:
  using iterator = Lit*;
  using const_iterator = Lit const*;
  using size_type = uint32_t;

  iterator begin() noexcept { return &m_literals[0]; }
  iterator end() noexcept { return begin() + m_size; }

  const_iterator begin() const noexcept { return cbegin(); }
  const_iterator end() const noexcept { return cend(); }

  const_iterator cbegin() const noexcept { return &m_literals[0]; }
  const_iterator cend() const noexcept { return cbegin() + m_size; }

  Lit& operator[](size_type idx) noexcept
  {
    assert(idx < m_size);
    return m_literals[idx];
  }

  Lit const& operator[](size_type idx) const noexcept
  {
    assert(idx < m_size);
    return m_literals[idx];
  }

  size_type size() const noexcept
  {
    return m_size;
  }

  /// Number of bytes required by a clause containing 'size' literals.
  static size_t bytes(size_type size) noexcept
  {
    size_t const embedded_literals = std::extent_v<decltype(m_literals)>;
    size_t const additional_literals = (size >= embedded_literals) ? (size - embedded_literals) : 0;
    size_t const total_bytes = sizeof(Clause) + sizeof(Lit) * additional_literals;
    return total_bytes;
  }

private:
  // NOTE: do not use this constructor directly
  // because it does not allocate enough memory for the literals
  Clause(size_type size) noexcept
      : m_size{size}
  { }

  // cannot copy/move because of flexible array member
  Clause(Clause&) = delete;
  Clause(Clause&&) = delete;
  Clause& operator=(Clause&) = delete;
  Clause& operator=(Clause&&) = delete;

  friend class ClauseArena;
  friend class AllocatedClause;

private:
  size_type m_size;    // number of literals
  Lit m_literals[2];  // actual size is m_size, but C++ does not officially support flexible array members (as opposed to C)
}; // Clause

std::ostream& operator<<(std::ostream& os, Clause const& c)
{
  os << "{ ";
  bool first = true;
  for (Lit lit : c) {
    if (first) {
      first = false;
    } else {
      os << ", ";
    }
    os << lit;
  }
  os << " }";
  return os;
}





class ClauseRef final
{
public:
  using index_type = std::uint32_t;

  /// Create an invalid ClauseRef.
  [[nodiscard]] static constexpr ClauseRef invalid() noexcept
  {
    return ClauseRef{std::numeric_limits<index_type>::max()};
  }

  [[nodiscard]] static constexpr index_type max_index() noexcept
  {
    return std::numeric_limits<index_type>::max() - 1;
  }

  constexpr bool is_valid() const noexcept
  {
    return m_index != invalid().m_index;
  }

  constexpr index_type index() const noexcept
  {
    return m_index;
  }

private:
  explicit constexpr ClauseRef(index_type index) noexcept
      : m_index{index}
  { }

  // friend class Watch;
  friend class ClauseArena;

private:
  /// Index into the arena storage.
  index_type m_index;
#ifndef NDEBUG
  /// Timestamp to check for invalid clause references (debug mode only).
  std::uint32_t m_timestamp = 123456;
#endif
};

[[nodiscard]] constexpr bool operator==(ClauseRef lhs, ClauseRef rhs) noexcept
{
  return lhs.index() == rhs.index();
}

[[nodiscard]] constexpr bool operator!=(ClauseRef lhs, ClauseRef rhs) noexcept
{
  return !operator==(lhs, rhs);
}

std::ostream& operator<<(std::ostream& os, ClauseRef cr)
{
  os << "ClauseRef{" << cr.index() << "}";
  return os;
}




class AllocatedClause
{
public:
  void push(Lit lit)
  {
    assert(m_clause);
    assert(m_clause->m_size < m_capacity);
    m_clause->m_literals[m_clause->m_size] = lit;
    m_clause->m_size += 1;
  }

  ClauseRef build()
  {
    assert(m_clause);
#ifndef NDEBUG
    m_clause = nullptr;
#endif
    return m_ref;
  }

private:
  AllocatedClause(Clause& clause, ClauseRef ref, uint32_t capacity)
      : m_clause{&clause}
      , m_ref{ref}
#ifndef NDEBUG
      , m_capacity{capacity}
#endif
  {
    assert(m_clause);
    assert(capacity >= 2);
  }

  friend class ClauseArena;

private:
  Clause* m_clause;
  ClauseRef m_ref;
#ifndef NDEBUG
  uint32_t m_capacity;
#endif
};





class ClauseArena final
{
private:
  using storage_type = std::uint32_t;
  static_assert(alignof(Clause) == alignof(storage_type), "Clause alignment mismatch");
  // Maybe the more correct condition is this (storage alignment must be a multiple of clause alignment):
  static_assert(alignof(storage_type) % alignof(Clause) == 0, "Alignment of storage must imply alignment of clause");
  static_assert(std::is_trivially_destructible_v<Clause>, "Clause destructor must be trivial because we never call it");

  void* deref_plain(ClauseRef ref)
  {
    assert(ref.is_valid());
    assert(ref.m_timestamp == m_timestamp);
    return &m_storage[ref.m_index];
  }

  void const* deref_plain(ClauseRef ref) const
  {
    assert(ref.is_valid());
    assert(ref.m_timestamp == m_timestamp);
    return &m_storage[ref.m_index];
  }

public:
  Clause& deref(ClauseRef ref)
  {
    return *reinterpret_cast<Clause*>(deref_plain(ref));
  }

  Clause const& deref(ClauseRef ref) const
  {
    return *reinterpret_cast<Clause const*>(deref_plain(ref));
  }

  /// Allocate a new clause with enough space for 'capacity' literals.
  AllocatedClause alloc(std::uint32_t capacity)
  {
    std::size_t const old_size = m_storage.size();
    if (old_size > static_cast<std::size_t>(ClauseRef::max_index())) {
      std::cerr << "ClauseArena::alloc: too many stored literals, unable to represent additional clause reference" << std::endl;
      throw std::bad_alloc();
    }

    std::size_t const bytes = Clause::bytes(capacity);
    assert(bytes % sizeof(storage_type) == 0);
    std::size_t const elements = bytes / sizeof(storage_type);
    std::size_t const new_size = old_size + elements;

    // TODO: avoid zero-initialization of vector elements by using custom allocator, or just don't use std::vector for the buffer...
    m_storage.resize(new_size);

    ClauseRef ref(old_size);
#ifndef NDEBUG
    ref.m_timestamp = m_timestamp;
#endif
    void* p = deref_plain(ref);
    Clause* c = new (p) Clause{0};
    return AllocatedClause{*c, ref, capacity};
  }

  /// Remove all clauses from the arena.
  /// All existing clause references are invalidated.
  /// The backing storage is not deallocated.
  void clear() noexcept
  {
    m_storage.clear();
#ifndef NDEBUG
    m_timestamp += 1;
#endif
  }

  /// Allocate storage for 'capacity' literals.
  /// Note that the actual space for literals will be less, since clause headers is stored in the same space.
  void reserve(std::size_t capacity)
  {
    m_storage.reserve(capacity);
  }

  // TODO: iterator over clauses, counter for #clauses stored
  //       hmm, we may have gaps. so we can't iterate easily.

private:
  std::vector<storage_type> m_storage;
#ifndef NDEBUG
  /// Timestamp to check for invalid clause references (debug mode only).
  std::uint32_t m_timestamp = 0;
#endif
};



} // namespace SMTSubsumption

#endif /* !CLAUSE_HPP */
