/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef DECISION_QUEUE_HPP
#define DECISION_QUEUE_HPP

#include "./log.hpp"
#include "./vector_map.hpp"
#include "./types.hpp"

namespace subsat {


/// Doubly-linked queue for variable-move-to-front (VMTF) decision heuristic.
class DecisionQueue
{
private:
  template< typename Key
          , typename Compare = std::less<Key>
          >
  using set = std::set<Key, Compare, allocator_type<Key>>;

  using Timestamp = uint32_t;

  struct Link
  {
    Var prev = Var::invalid();
    Var next = Var::invalid();
    /// Timestamp of last enqueue operation.
    Timestamp stamp;
#ifndef NDEBUG
    bool enqueued = false;
#endif
  };

public:
  bool empty() const noexcept
  {
    bool const is_empty = m_links.empty();
    if (is_empty) {
      assert(m_first == Var::invalid());
      assert(m_last == Var::invalid());
      assert(m_search == Var::invalid());
      assert(m_stamp == 0);
    }
    return is_empty;
  }

  void clear() noexcept
  {
    m_links.clear();
    m_first = Var::invalid();
    m_last = Var::invalid();
    m_search = Var::invalid();
    m_stamp = 0;
    assert(empty());
  }

  void reserve(uint32_t var_count)
  {
    m_links.reserve(var_count);
  }

  void resize_and_init(uint32_t var_count)
  {
    assert(m_links.size() <= UINT32_MAX);
    uint32_t const old_var_count = static_cast<uint32_t>(m_links.size());

    m_links.resize(var_count);  // TODO: should not initialize memory here
    for (uint32_t idx = old_var_count; idx < var_count; ++idx) {
      enqueue(Var{idx});
    }
    m_search = m_last;
  }

  /// Move variable to front of decision queue.
  /// Precondition: variable must be assigned (otherwise the search position cache will be incorrect).
  void move_to_front(Var var)
  {
    if (var != m_last) {
      dequeue(var);
      enqueue(var);
    }
  }

  /// Finds the next unassigned variable.
  /// Precondition: at least one variable is unassigned.
  Var next_unassigned_variable(vector_map<Lit, Value> const& values)
  {
    assert(std::any_of(values.begin(), values.end(), [](Value x){ return x == Value::Unassigned; }));
    Var var = m_search;
    while (true) {
      assert(var.is_valid());
      if (values[var] == Value::Unassigned) {
        // We will always reach this point because all unassigned variables
        // are to the left of the search position cache.
        break;
      } else {
        var = m_links[var].prev;
        assert(var.is_valid());
      }
    }
    m_search = var;
    LOG_DEBUG("VMTF decision variable " << var << " with stamp " << m_links[var].stamp);
    return var;
  }

  /// Updates the search position cache when a variable is unassigned.
  void unassign(Var var)
  {
    if (m_links[m_search].stamp < m_links[var].stamp) {
      m_search = var;
    }
  }

#ifndef NDEBUG
  bool checkInvariants(vector_map<Lit, Value> const& values) const
  {
    if (m_first.is_valid()) {
      assert(m_last.is_valid());
      assert(m_search.is_valid());
    } else {
      assert(!m_last.is_valid());
      assert(!m_search.is_valid());
    }

    set<Var> seen;

    // Forward traversal
    Timestamp stamp = 0;
    Var prev = Var::invalid();
    for (Var var = m_first; var.is_valid();) {
      Link const& link = m_links[var];
      // Check that there are no cycles
      bool inserted = seen.insert(var).second;
      assert(inserted);
      // Check pointers
      assert(link.prev == prev);
      // Check timestamp order
      assert(var == m_first || stamp < link.stamp);
      assert(link.stamp < m_stamp);
      stamp = link.stamp;
      prev = var;
      var = link.next;
    }
    assert(seen.size() == m_links.size());

    // Backward traversal
    seen.clear();
    Var next = Var::invalid();
    for (Var var = m_last; var.is_valid();) {
      Link const& link = m_links[var];
      // Check that there are no cycles
      bool inserted = seen.insert(var).second;
      assert(inserted);
      // Check pointers
      assert(link.next == next);
      next = var;
      var = link.prev;
    }
    assert(seen.size() == m_links.size());

    // Check search position cache
    // (there should be no unassigned variable after the cached search position)
    for (Var var = m_search; var.is_valid(); var = m_links[var].next) {
      if (var != m_search) {
        assert(values[var] != Value::Unassigned);
      }
    }

    return true;
  }  // checkInvariants
#endif

private:
  /// Remove variable from the queue.
  void dequeue(Var var)
  {
    LOG_TRACE(var);
    Link& link = m_links[var];
    assert(link.enqueued);
#ifndef NDEBUG
    link.enqueued = false;
#endif
    if (link.prev.is_valid()) {
      Link& prev = m_links[link.prev];
      assert(prev.next == var);
      prev.next = link.next;
    } else {
      assert(m_first == var);
      m_first = link.next;
    }
    if (link.next.is_valid()) {
      Link& next = m_links[link.next];
      assert(next.prev == var);
      next.prev = link.prev;
    } else {
      assert(m_last == var);
      m_last = link.prev;
    }
  }

  /// Enqueue variable at the end of the queue.
  void enqueue(Var var)
  {
    LOG_TRACE(var);
    Link& link = m_links[var];
    assert(!link.enqueued);
#ifndef NDEBUG
    link.enqueued = true;
#endif
    if (m_last.is_valid()) {
      assert(!m_links[m_last].next.is_valid());
      m_links[m_last].next = var;
    } else {
      assert(!m_first.is_valid());
      m_first = var;
    }
    link.prev = m_last;
    m_last = var;
    link.next = Var::invalid();

    link.stamp = m_stamp++;

    if (m_stamp == 0) {
      // Timestamp overflow happened
      restamp();
    }
  }

  /// Reassign enqueue timestamps to prevent overflow.
  void restamp()
  {
    LOG_INFO("restamping decision queue");
    Timestamp stamp = 0;
    for (Var v = m_first; v.is_valid(); v = m_links[v].next) {
      assert(stamp < std::numeric_limits<Timestamp>::max());
      m_links[v].stamp = ++stamp;
    }
    m_search = m_last;  // TODO: why?
    m_stamp = stamp;
  }

private:
  vector_map<Var, Link> m_links;
  Var m_first = Var::invalid();
  Var m_last = Var::invalid();
  /// Search position cache
  Var m_search = Var::invalid();
  Timestamp m_stamp = 0;
};


} // namespace subsat

#endif /* !DECISION_QUEUE_HPP */
