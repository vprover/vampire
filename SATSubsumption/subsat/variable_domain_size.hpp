/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#ifndef VARIABLE_DOMAIN_SIZE_HPP
#define VARIABLE_DOMAIN_SIZE_HPP

#include <limits>

#include "./vector_map.hpp"
#include "./types.hpp"
#include "./log.hpp"

namespace subsat {


/// Domain size decision heuristic, similar as in CSP solving.
///
/// A set of boolean variables representing the choices of a non-boolean variable ("value encoding")
/// is called a "group" in this class.  (nothing to do with mathematical groups, just variables "grouped together").
class VariableDomainSize final {
public:

  /// Group indices should form a contiguous range starting at 0.
  using Group = std::uint32_t;
  enum : Group {
    InvalidGroup = std::numeric_limits<Group>::max(),
  };

private:
  /// Internally, index 0 is used for the "invalid" group (to avoid branching in 'assigned'/'unassigned').
  /// InternalGroup == Group + 1.
  using InternalGroup = std::uint32_t;
  enum : InternalGroup {
    InvalidInternalGroup = 0,
  };
  static_assert(InvalidGroup + 1 == InvalidInternalGroup, "unexpected value");

  using GroupSize = std::uint32_t;

public:
  VariableDomainSize()
  {
    clear();
  }

  bool empty() const noexcept
  {
    bool const is_empty = m_var_groups.empty();
    if (is_empty) {
      assert(m_domain_sizes.size() == 1 && m_domain_sizes[0] == 0);
    }
    return is_empty;
  }

  void clear() noexcept
  {
    m_var_groups.clear();
    m_domain_sizes.clear();
    m_domain_sizes.push_back(0);  // for the invalid group
    assert(empty());
  }

  /// Like clear but keeps the variable groups.
  void clear_domain_sizes() noexcept
  {
    m_domain_sizes.clear();
    m_domain_sizes.push_back(0);  // for the invalid group
  }

  void reserve(uint32_t var_count, uint32_t group_count)
  {
    m_var_groups.reserve(var_count);
    m_domain_sizes.reserve(group_count);
  }

  /// Allocate space for variables up to 'v'.
  void ensure_var(Var v)
  {
    assert(v.is_valid());
    while (v.index() >= m_var_groups.size()) {
      m_var_groups.push_back(InvalidInternalGroup);
    }
  }

  /// Register a new (unassigned) variable with a group.
  /// Group indices should be contiguous starting from 0.
  void set_group(Var v, Group g)
  {
    assert(g != InvalidGroup);
    assert(v.is_valid());
    assert(v.index() < m_var_groups.size());
    assert(m_var_groups[v] == InvalidInternalGroup);  // the group should be set only once, otherwise we have to correctly de-register from previous group
    InternalGroup const ig = g + 1;
    // while (ig >= m_domain_sizes.size()) {
    //   m_domain_sizes.push_back(0);
    // }
    m_var_groups[v] = ig;
    // m_domain_sizes[ig] += 1;
    LOG_DEBUG("Adding variable " << v << " to group " << g /* << ", domain size now is " << m_domain_sizes[ig] */);
  }

  /// Call this after set_group has been called for all variables,
  /// and before using assigned/unassigned/select_min_domain.
  void prepare_for_solving()
  {
    for (InternalGroup const ig : m_var_groups) {
      while (ig >= m_domain_sizes.size()) {
        m_domain_sizes.push_back(0);
      }
      m_domain_sizes[ig] += 1;
    }
  }

  // TODO: rename on_assigned?
  void assigned(Var v)
  {
    assert(v.is_valid());
    assert(v.index() < m_var_groups.size());
    InternalGroup ig = m_var_groups[v];
    assert(ig < m_domain_sizes.size());
    m_domain_sizes[ig] -= 1;
    LOG_DEBUG("Assigned variable " << v << " of group " << (ig - 1) << ", domain size now is " << m_domain_sizes[ig]);
  }

  void unassigned(Var v)
  {
    assert(v.is_valid());
    assert(v.index() < m_var_groups.size());
    InternalGroup ig = m_var_groups[v];
    assert(ig < m_domain_sizes.size());
    m_domain_sizes[ig] += 1;
    LOG_DEBUG("Unassigned variable " << v << " of group " << (ig - 1) << ", domain size now is " << m_domain_sizes[ig]);
  }

  /// Select variable with the smallest non-zero domain size.
  Var select_min_domain(subsat::vector_map<Lit, Value> const& values)
  {
    assert(check_invariants(values));
    // TODO: for now, we just do a simple linear search
    //       a smarter algorithm could mark the whole group as inactive as soon as one variable from it is assigned to TRUE (the others will be immediately propagated false by the theory propagator [this is because Vampire first applies duplicate literal removal -- so there cannot be another match with compatible bindings]).
    // TODO: for now, we choose the first unassigned variable from the group. Maybe we should choose the most "recent" one (recent in the VMTF sense), or something else?
    // Find group with minimal non-zero size
    InternalGroup sg = InvalidInternalGroup;
    GroupSize sg_size = std::numeric_limits<uint32_t>::max();
    for (InternalGroup ig = 1; ig < m_domain_sizes.size(); ++ig) {
      GroupSize const g_size = m_domain_sizes[ig];
      if (0 < g_size && g_size < sg_size) {
        sg = ig;
        sg_size = g_size;
      }
    }
    // Find an unassigned variable from that group, we simply return the first one.
    for (Var::index_type idx = 0; idx < m_var_groups.size(); ++idx) {
      Var v{idx};
      if (m_var_groups[v] == sg && values[v] == Value::Unassigned) {
        LOG_INFO("Domain size: choose variable " << v << " of group " << sg << " with size " << sg_size);
        return v;
      }
    }
    // This will only be reached if all variables are assigned, but then we don't make a decision.
    LOG_INFO("Domain size: no valid choice");
    return Var::invalid();
  }

#ifndef NDEBUG
  bool check_invariants(subsat::vector_map<Lit, Value> const& values) const
  {
    for (InternalGroup ig = 1; ig < m_domain_sizes.size(); ++ig) {
      uint32_t unassigned_count = 0;
      for (Var::index_type idx = 0; idx < m_var_groups.size(); ++idx) {
        Var v{idx};
        if (m_var_groups[v] == ig && values[v] == Value::Unassigned) {
          unassigned_count += 1;
        }
      }
      assert(m_domain_sizes[ig] == unassigned_count);
    }
    return true;
  }
#endif

private:
  /// For each variable, the group it belongs to.
  vector_map<Var, InternalGroup> m_var_groups;

  /// The number of unassigned variables belonging to each group.
  vector_map<InternalGroup, GroupSize> m_domain_sizes;
};


}  // namespace subsat

#endif /* !VARIABLE_DOMAIN_SIZE_HPP */
