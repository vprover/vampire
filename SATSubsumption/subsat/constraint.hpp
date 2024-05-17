/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef SUBSAT_CONSTRAINT_HPP
#define SUBSAT_CONSTRAINT_HPP

#include <iostream>
#include <random>
#include <type_traits>
#include <vector>

#include "./default_init_allocator.hpp"
#include "./types.hpp"
#include "./log.hpp"

namespace subsat {





/// A constraint represented by an array of literals.
/// We use this for both clauses and at-most-one constraints.
class Constraint final
{
public:
  enum class Kind {
    Clause,
    AtMostOne,
  };

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

  /// Number of bytes required for the constraint header (without literals).
  static constexpr size_t header_bytes() noexcept
  {
    size_t constexpr embedded_literals = std::extent_v<decltype(m_literals)>;
    size_t constexpr header_bytes = sizeof(Constraint) - sizeof(Lit) * embedded_literals;
    static_assert(header_bytes == offsetof(Constraint, m_literals));
    return header_bytes;
  }

  /// Number of bytes required by a constraint containing 'size' literals.
  static constexpr size_t bytes(size_type size) noexcept
  {
    size_t const embedded_literals = std::extent_v<decltype(m_literals)>;
    size_t const additional_literals = (size >= embedded_literals) ? (size - embedded_literals) : 0;
    size_t const total_bytes = sizeof(Constraint) + sizeof(Lit) * additional_literals;
    return total_bytes;
  }

private:
  // NOTE: do not use this constructor directly
  // because it does not allocate enough memory for the literals
  Constraint(size_type size) noexcept
      : m_size{size}
  { }

  // cannot copy/move because of flexible array member
  Constraint(Constraint&) = delete;
  Constraint(Constraint&&) = delete;
  Constraint& operator=(Constraint&) = delete;
  Constraint& operator=(Constraint&&) = delete;

  friend class ConstraintArena;
  friend class Solver;

private:
  size_type m_size;   // number of literals
  Lit m_literals[2];  // actual size is m_size, but C++ does not officially support flexible array members (as opposed to C)
};  // Constraint

std::ostream& operator<<(std::ostream& os, Constraint const& c);





/// Reference to a constraint stored in a ConstraintArena.
class ConstraintRef final
{
public:
  using index_type = std::uint32_t;

  /// Create an invalid ConstraintRef.
  [[nodiscard]] static constexpr ConstraintRef invalid() noexcept
  {
    return ConstraintRef{std::numeric_limits<index_type>::max()};
  }

  [[nodiscard]] static constexpr index_type max_index() noexcept
  {
    return std::numeric_limits<index_type>::max() - 1;
  }

  [[nodiscard]] constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  [[nodiscard]] constexpr index_type index() const noexcept
  {
    return m_index;
  }

private:
  explicit constexpr ConstraintRef(index_type index) noexcept
      : m_index{index}
  { }

  friend class ConstraintArena;

private:
  /// Index into the arena storage.
  index_type m_index;
#ifndef NDEBUG
  /// Arena id to check for mismatched constraint references (debug mode only).
  std::uint32_t m_arena_id = 123456;
#endif
};
static_assert(std::is_trivially_destructible<ConstraintRef>::value, "");

[[nodiscard]] constexpr bool operator==(ConstraintRef lhs, ConstraintRef rhs) noexcept
{
  return lhs.index() == rhs.index();
}

[[nodiscard]] constexpr bool operator!=(ConstraintRef lhs, ConstraintRef rhs) noexcept
{
  return !operator==(lhs, rhs);
}

std::ostream& operator<<(std::ostream& os, ConstraintRef cr);





class AllocatedConstraintHandle final
{
private:
  AllocatedConstraintHandle(ConstraintRef constraint_ref, uint32_t capacity) noexcept
      : m_constraint_ref{constraint_ref}
#ifndef NDEBUG
      , m_capacity{capacity}
#endif
  {
    (void)capacity;
  }

  friend class ConstraintArena;

private:
  ConstraintRef m_constraint_ref;
#ifndef NDEBUG
  uint32_t m_capacity;
#endif
};

static_assert(std::is_trivially_destructible<AllocatedConstraintHandle>::value, "");





class ConstraintArena final
{
private:
  using storage_type = std::uint32_t;
  static_assert(alignof(Constraint) == alignof(storage_type), "Constraint alignment mismatch");
  // Maybe the more correct condition is this (storage alignment must be a multiple of Constraint alignment):
  static_assert(alignof(storage_type) % alignof(Constraint) == 0, "Alignment of storage must imply alignment of Constraint");
  static_assert(std::is_trivially_destructible<Constraint>::value, "Constraint destructor must be trivial because we never call it");

  [[nodiscard]] void* deref_plain(ConstraintRef cr) noexcept
  {
    assert(cr.is_valid());
    assert(cr.m_arena_id == m_arena_id);
    return &m_storage[cr.m_index];
  }

  [[nodiscard]] void const* deref_plain(ConstraintRef cr) const noexcept
  {
    assert(cr.is_valid());
    assert(cr.m_arena_id == m_arena_id);
    return &m_storage[cr.m_index];
  }

public:
  ConstraintArena()
  {
#ifndef NDEBUG
    static thread_local std::mt19937 gen(123);
    std::uniform_int_distribution<uint32_t> d{0, std::numeric_limits<uint32_t>::max()};
    m_arena_id = d(gen);
#endif
  }

  [[nodiscard]] Constraint& deref(ConstraintRef cr) noexcept
  {
    return *reinterpret_cast<Constraint*>(deref_plain(cr));
  }

  [[nodiscard]] Constraint const& deref(ConstraintRef cr) const noexcept
  {
    return *reinterpret_cast<Constraint const*>(deref_plain(cr));
  }

  /// Allocate a new constraint with enough space for 'capacity' literals.
  /// May throw std::bad_alloc if the arena is exhausted, or reallocating the arena fails.
  [[nodiscard]] AllocatedConstraintHandle alloc(std::uint32_t capacity)
  {
    assert(!m_dynamic_ref.is_valid());

    ConstraintRef cr = make_ref();

    std::size_t const bytes = Constraint::bytes(capacity);
    assert(bytes % sizeof(storage_type) == 0);
    std::size_t const elements = bytes / sizeof(storage_type);
    std::size_t const new_size = m_storage.size() + elements;
    LOG_TRACE("Allocating " << elements << " elements for capacity " << capacity << " (old storage size: " << m_storage.size() << ", new: " << new_size << ")");

    m_storage.resize(new_size);

    void* p = deref_plain(cr);
    Constraint* c = new (p) Constraint{0};
    assert(c);
    (void)c;  // suppress "unused variable" warning
    return AllocatedConstraintHandle{cr, capacity};
  }

  void handle_push_literal(AllocatedConstraintHandle& handle, Lit lit) noexcept
  {
    assert(handle.m_constraint_ref.is_valid());
    Constraint& c = deref(handle.m_constraint_ref);
    assert(c.m_size < handle.m_capacity);
    c.m_literals[c.m_size] = lit;
    c.m_size += 1;
  }

  [[nodiscard]] ConstraintRef handle_build(AllocatedConstraintHandle& handle) noexcept
  {
    assert(handle.m_constraint_ref.is_valid());
    ConstraintRef cr = handle.m_constraint_ref;
#ifndef NDEBUG
    handle.m_constraint_ref = ConstraintRef::invalid();
#endif
    return cr;
  }

  /// Start a new constraint of unknown size at the end of the current storage.
  /// Only one of these can be active at a time, and alloc cannot be used while this is active.
  void start()
  {
    assert(!m_dynamic_ref.is_valid());

    m_dynamic_ref = make_ref();

    std::size_t constexpr header_bytes = Constraint::header_bytes();
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

  [[nodiscard]] ConstraintRef end() noexcept
  {
    assert(m_dynamic_ref.is_valid());

    std::size_t const old_size = m_dynamic_ref.m_index;
    std::size_t constexpr header_elements = Constraint::header_bytes() / sizeof(storage_type);
    assert(m_storage.size() >= old_size + header_elements);
    std::size_t const c_size = m_storage.size() - old_size - header_elements;

    ConstraintRef cr = m_dynamic_ref;
    Constraint& c = deref(cr);
    c.m_size = static_cast<Constraint::size_type>(c_size);

    m_dynamic_ref = ConstraintRef::invalid();
    return cr;
  }

  /// Delete the given constraint and all that were added afterwards!
  void unsafe_delete(ConstraintRef cr)
  {
    assert(cr.is_valid());
    assert(cr.m_arena_id == m_arena_id);
    assert(!m_dynamic_ref.is_valid());
    m_storage.resize(cr.m_index);
  }

  /// Remove all constraints from the arena.
  /// All existing constraint references are invalidated.
  /// The backing storage is not deallocated.
  void clear() noexcept
  {
    m_storage.clear();
    m_dynamic_ref = ConstraintRef::invalid();
#ifndef NDEBUG
    m_arena_id += 1;
#endif
    assert(empty());
  }

  [[nodiscard]] bool empty() const noexcept
  {
    bool const is_empty = m_storage.empty();
    if (is_empty) {
      assert(!m_dynamic_ref.is_valid());
    }
    return is_empty;
  }

  /// Allocate storage for 'capacity' literals.
  /// Note that the actual space for literals will be less, since constraint headers is stored in the same space.
  void reserve(std::size_t capacity)
  {
    m_storage.reserve(capacity);
  }

  /// Returns the amount of storage used (actually used, not allocated).
  [[nodiscard]] std::size_t size() const noexcept
  {
    return m_storage.size();
  }

  /// Returns the amount of allocated storage.
  [[nodiscard]] std::size_t capacity() const noexcept
  {
    return m_storage.capacity();
  }

private:
  [[nodiscard]] ConstraintRef make_ref()
  {
    std::size_t const size = m_storage.size();
    if (size > static_cast<std::size_t>(ConstraintRef::max_index())) {
      std::cerr << "ConstraintArena::alloc: too many stored literals, unable to represent additional constraint reference" << std::endl;
      throw std::bad_alloc();
    }
    ConstraintRef cr(static_cast<ConstraintRef::index_type>(size));
#ifndef NDEBUG
    cr.m_arena_id = m_arena_id;
#endif
    return cr;
  }

private:
  // NOTE: we use the default_init_allocator to avoid zero-initialization when resizing m_storage
  std::vector<storage_type, default_init_allocator<storage_type, allocator_type<storage_type>>> m_storage;
#ifndef NDEBUG
  /// Arena id allows to check for constraint references coming from wrong or cleared arenas (debug mode only).
  std::uint32_t m_arena_id;
#endif
  ConstraintRef m_dynamic_ref = ConstraintRef::invalid();
};





} // namespace subsat

#endif /* !SUBSAT_CONSTRAINT_HPP */
