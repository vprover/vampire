/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef VECTOR_MAP_HPP
#define VECTOR_MAP_HPP

#include <cstdint>
#include <vector>
#include "Debug/Assertion.hpp"

namespace subsat { // TODO: remove namespace once I separate out Var/Lit from subsat.hpp

/// Get index by calling a member function 'index()'.
template <typename Key>
struct IndexMember {
  using key_type = Key;
  using index_type = std::invoke_result_t<decltype(&key_type::index), Key>;
  index_type operator()(Key key) const
  {
    return key.index();
  }
};

/// The type itself is already the index.
template <typename Integer>
struct IndexIdentity {
  Integer operator()(Integer key) const noexcept
  {
    return key;
  }
};

/// Allows to defines a default indexing method for types.
template <typename Key>
struct DefaultIndex;

template <>
struct DefaultIndex<std::uint32_t> {
  using type = IndexIdentity<std::uint32_t>;
};

template <typename Key>
using DefaultIndex_t = typename DefaultIndex<Key>::type;

/// Vector-based map with type-safe indexing.
/// This class simply replaces vector's integral index by a newtype wrapper,
/// so this class should only be used if the keys can be mapped easily to a range [0..n].
template <
    typename Key,
    typename T,
    typename Allocator = std::allocator<T>,
    typename Indexing = DefaultIndex_t<Key>>
class vector_map_t final {
public:
  using key_type = Key;
  using value_type = T;
  using indexing_type = Indexing;
  using allocator_type = Allocator;
  using vector_type = std::vector<value_type, Allocator>;
  using reference = value_type&;
  using const_reference = value_type const&;
  using size_type = typename vector_type::size_type;
  using iterator = typename vector_type::iterator;
  using const_iterator = typename vector_type::const_iterator;

  reference operator[](key_type key)
  {
    size_type const idx = index(key);
    ASS(idx < size());
    return m_data[idx];
  }

  const_reference operator[](key_type key) const
  {
    size_type const idx = index(key);
    ASS(idx < size());
    return m_data[idx];
  }

  bool contains(key_type key) const
  {
    size_type const idx = index(key);
    return idx < size();
  }

  void reserve(size_type new_cap) { m_data.reserve(new_cap); }

  bool empty() const noexcept { return m_data.empty(); }
  size_type size() const noexcept { return m_data.size(); }

  iterator begin() noexcept { return m_data.begin(); }
  const_iterator begin() const noexcept { return m_data.begin(); }
  const_iterator cbegin() const noexcept { return m_data.cbegin(); }
  iterator end() noexcept { return m_data.end(); }
  const_iterator end() const noexcept { return m_data.end(); }
  const_iterator cend() const noexcept { return m_data.cend(); }

  // TODO: a map-like iterator would be nice. need to extend Index with the backward conversion.
  //       Also, key_begin(), key_end(), key_view() to iterate over indices.

  void clear() noexcept { m_data.clear(); }

  void push_back(T const& value) { m_data.push_back(value); }
  void push_back(T&& value) { m_data.push_back(std::move(value)); }

  template <typename... Args>
  reference emplace_back(Args&&... args)
  {
    return m_data.emplace_back(std::forward<Args>(args)...);
  }

  void resize(size_type count) { m_data.resize(count); }
  void resize(size_type count, value_type const& value) { m_data.resize(count, value); }

  vector_type const& underlying() const
  {
    return m_data;
  }

private:
  size_type index(Key key) const
  {
    indexing_type index;
    return index(key);
  }

private:
  vector_type m_data;
};

} // namespace subsat

#endif /* !VECTOR_MAP_HPP */
