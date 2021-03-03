#ifndef CLAUSE_HPP
#define CLAUSE_HPP

#include <iostream>
#include <type_traits>
#include <vector>

#include "./default_init_allocator.hpp"
#include "./types.hpp"

namespace subsat {

// TODO: rename Clause -> Constraint, since we use the same types for AMO-constraints now too

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

  /// Number of bytes required for the clause header (without literals).
  static constexpr size_t header_bytes() noexcept
  {
#if __cplusplus >= 201703L
    size_t constexpr embedded_literals = std::extent_v<decltype(m_literals)>;
    size_t constexpr header_bytes = sizeof(Clause) - sizeof(Lit) * embedded_literals;
    static_assert(header_bytes == offsetof(Clause, m_literals));
    return header_bytes;
#else
    return sizeof(Clause) - sizeof(Lit) * std::extent<decltype(m_literals)>::value;
#endif
  }

  /// Number of bytes required by a clause containing 'size' literals.
  static size_t bytes(size_type size) noexcept
  {
#if __cplusplus >= 201703L
    size_t const embedded_literals = std::extent_v<decltype(m_literals)>;
    size_t const additional_literals = (size >= embedded_literals) ? (size - embedded_literals) : 0;
    size_t const total_bytes = sizeof(Clause) + sizeof(Lit) * additional_literals;
    return total_bytes;
#else
    return sizeof(Clause) + sizeof(Lit) * ((size >= std::extent<decltype(m_literals)>::value) ? (size - std::extent<decltype(m_literals)>::value) : 0);
#endif
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

  template <template <typename> class Allocator> friend class ClauseArena;
  template <template <typename> class Allocator> friend class Solver;

private:
  size_type m_size;    // number of literals
  Lit m_literals[2];  // actual size is m_size, but C++ does not officially support flexible array members (as opposed to C)
}; // Clause

static std::ostream& operator<<(std::ostream& os, Clause const& c)
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
  NODISCARD static constexpr ClauseRef invalid() noexcept
  {
    return ClauseRef{std::numeric_limits<index_type>::max()};
  }

  NODISCARD static constexpr index_type max_index() noexcept
  {
    return std::numeric_limits<index_type>::max() - 1;
  }

  NODISCARD constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  NODISCARD constexpr index_type index() const noexcept
  {
    return m_index;
  }

private:
  explicit constexpr ClauseRef(index_type index) noexcept
      : m_index{index}
  { }

  template <template <typename> class Allocator> friend class ClauseArena;

private:
  /// Index into the arena storage.
  index_type m_index;
#ifndef NDEBUG
  /// Timestamp to check for invalid clause references (debug mode only).
  std::uint32_t m_timestamp = 123456;
#endif
};
static_assert(std::is_trivially_destructible<ClauseRef>::value, "");

NODISCARD constexpr bool operator==(ClauseRef lhs, ClauseRef rhs) noexcept
{
  return lhs.index() == rhs.index();
}

NODISCARD constexpr bool operator!=(ClauseRef lhs, ClauseRef rhs) noexcept
{
  return !operator==(lhs, rhs);
}

static std::ostream& operator<<(std::ostream& os, ClauseRef cr)
{
  os << "ClauseRef{";
  if (cr.is_valid()) {
    os << cr.index();
  } else {
    os << "-";
  }
  os << "}";
  return os;
}




class AllocatedClauseHandle final
{
private:
  AllocatedClauseHandle(ClauseRef clause_ref, uint32_t capacity) noexcept
      : m_clause_ref{clause_ref}
#ifndef NDEBUG
      , m_capacity{capacity}
#endif
  {
    (void)capacity;
  }

  template <template <typename> class Allocator> friend class ClauseArena;

private:
  ClauseRef m_clause_ref;
#ifndef NDEBUG
  uint32_t m_capacity;
#endif
};

static_assert(std::is_trivially_destructible<AllocatedClauseHandle>::value, "");





template <template <typename> class Allocator = std::allocator>
class ClauseArena final
{
private:
  using storage_type = std::uint32_t;
  static_assert(alignof(Clause) == alignof(storage_type), "Clause alignment mismatch");
  // Maybe the more correct condition is this (storage alignment must be a multiple of clause alignment):
  static_assert(alignof(storage_type) % alignof(Clause) == 0, "Alignment of storage must imply alignment of clause");
  static_assert(std::is_trivially_destructible<Clause>::value, "Clause destructor must be trivial because we never call it");

  NODISCARD void* deref_plain(ClauseRef cr) noexcept
  {
    assert(cr.is_valid());
    assert(cr.m_timestamp == m_timestamp);
    return &m_storage[cr.m_index];
  }

  NODISCARD void const* deref_plain(ClauseRef cr) const noexcept
  {
    assert(cr.is_valid());
    assert(cr.m_timestamp == m_timestamp);
    return &m_storage[cr.m_index];
  }

public:
  template <typename T>
  using allocator_type = Allocator<T>;

  NODISCARD Clause& deref(ClauseRef cr) noexcept
  {
    return *reinterpret_cast<Clause*>(deref_plain(cr));
  }

  NODISCARD Clause const& deref(ClauseRef cr) const noexcept
  {
    return *reinterpret_cast<Clause const*>(deref_plain(cr));
  }

  /// Allocate a new clause with enough space for 'capacity' literals.
  /// May throw std::bad_alloc if the arena is exhausted, or reallocating the arena fails.
  NODISCARD AllocatedClauseHandle alloc(std::uint32_t capacity)
  {
    assert(!m_dynamic_ref.is_valid());

    ClauseRef cr = make_ref();

    std::size_t const bytes = Clause::bytes(capacity);
    assert(bytes % sizeof(storage_type) == 0);
    std::size_t const elements = bytes / sizeof(storage_type);
    std::size_t const new_size = m_storage.size() + elements;

    m_storage.resize(new_size);

    void* p = deref_plain(cr);
    Clause* c = new (p) Clause{0};
    assert(c);
    return AllocatedClauseHandle{cr, capacity};
  }

  void handle_push_literal(AllocatedClauseHandle& handle, Lit lit) noexcept
  {
    assert(handle.m_clause_ref.is_valid());
    Clause& clause = deref(handle.m_clause_ref);
    assert(clause.m_size < handle.m_capacity);
    clause.m_literals[clause.m_size] = lit;
    clause.m_size += 1;
  }

  NODISCARD ClauseRef handle_build(AllocatedClauseHandle& handle) noexcept
  {
    assert(handle.m_clause_ref.is_valid());
    ClauseRef cr = handle.m_clause_ref;
#ifndef NDEBUG
    handle.m_clause_ref = ClauseRef::invalid();
#endif
    return cr;
  }

  /// Start a new clause of unknown size at the end of the current storage.
  /// Only one of these can be active at a time, and alloc_clause cannot be used while this is active.
  void start()
  {
    assert(!m_dynamic_ref.is_valid());

    m_dynamic_ref = make_ref();

    std::size_t constexpr header_bytes = Clause::header_bytes();
    static_assert(header_bytes % sizeof(storage_type) == 0, "");
    std::size_t constexpr header_elements = header_bytes / sizeof(storage_type);
    std::size_t const new_size = m_storage.size() + header_elements;

    m_storage.resize(new_size);
  }

  void push_literal(Lit lit)
  {
    assert(m_dynamic_ref.is_valid());
    assert(lit.is_valid());
    m_storage.push_back(lit.index());
  }

  NODISCARD ClauseRef end()
  {
    assert(m_dynamic_ref.is_valid());

    std::size_t const old_size = m_dynamic_ref.m_index;
    std::size_t constexpr header_elements = Clause::header_bytes() / sizeof(storage_type);
    assert(m_storage.size() >= old_size + header_elements);
    std::size_t const clause_size = m_storage.size() - old_size - header_elements;

    ClauseRef cr = m_dynamic_ref;
    Clause& c = deref(cr);
    c.m_size = static_cast<Clause::size_type>(clause_size);

    m_dynamic_ref = ClauseRef::invalid();
    return cr;
  }

  /// Remove all clauses from the arena.
  /// All existing clause references are invalidated.
  /// The backing storage is not deallocated.
  void clear() noexcept
  {
    m_storage.clear();
    m_dynamic_ref = ClauseRef::invalid();
#ifndef NDEBUG
    m_timestamp += 1;
    m_clause_refs.clear();
#endif
    assert(empty());
  }

  bool empty() const noexcept
  {
    bool const is_empty = m_storage.empty();
    if (is_empty) {
      assert(!m_dynamic_ref.is_valid());
      assert(m_clause_refs.empty());
    }
    return is_empty;
  }

  /// Allocate storage for 'capacity' literals.
  /// Note that the actual space for literals will be less, since clause headers is stored in the same space.
  void reserve(std::size_t capacity)
  {
    m_storage.reserve(capacity);
  }

#ifndef NDEBUG
  using const_iterator = std::vector<ClauseRef>::const_iterator;
  const_iterator begin() const noexcept { return m_clause_refs.begin(); }
  const_iterator end() const noexcept { return m_clause_refs.end(); }
#endif

private:
  NODISCARD ClauseRef make_ref()
  {
    std::size_t const size = m_storage.size();
    if (size > static_cast<std::size_t>(ClauseRef::max_index())) {
      std::cerr << "ClauseArena::alloc: too many stored literals, unable to represent additional clause reference" << std::endl;
      throw std::bad_alloc();
    }
    ClauseRef cr(static_cast<ClauseRef::index_type>(size));
#ifndef NDEBUG
    cr.m_timestamp = m_timestamp;
    m_clause_refs.emplace_back(cr);
#endif
    return cr;
  }

private:
  // NOTE: we use the default_init_allocator to avoid zero-initialization when resizing m_storage
  std::vector<storage_type, default_init_allocator<storage_type, allocator_type<storage_type>>> m_storage;
#ifndef NDEBUG
  /// Timestamp to check for invalid clause references (debug mode only).
  /// TODO: start with a random timestamp instead of 0. Then we effectively check for different arenas as well!
  /// (then just name it m_arena_id, and also set randomly on clear()... we don't need "timestamp semantics" for this)
  std::uint32_t m_timestamp = 0;
  /// List of references to all clauses that have been added to the storage.
  std::vector<ClauseRef, allocator_type<ClauseRef>> m_clause_refs;
#endif
  ClauseRef m_dynamic_ref = ClauseRef::invalid();
};



} // namespace subsat

#endif /* !CLAUSE_HPP */
