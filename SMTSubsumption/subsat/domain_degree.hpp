#ifndef DOMAIN_DEGREE_HPP
#define DOMAIN_DEGREE_HPP

#include <limits>

#include "./vector_map.hpp"
#include "./types.hpp"
#include "./log.hpp"

namespace subsat {


/// Domain degree decision heuristic, similar as in CSP solving.
///
/// A set of boolean variables representing the choices of a non-boolean variable ("value encoding")
/// is called a "group" in this class.  (nothing to do with mathematical groups, just variables "grouped together").
template <template <typename> class Allocator = std::allocator>
class DomainDegree final {
public:
  template <typename T>
  using allocator_type = Allocator<T>;

  using Group = std::uint32_t;
  // inline static constexpr Group InvalidGroup = std::numeric_limits<Group>::max();
  enum : Group {
    InvalidGroup = std::numeric_limits<Group>::max(),
  };

  using GroupSize = std::uint32_t;

  bool empty() const noexcept
  {
    bool const is_empty = m_groups.empty();
    if (is_empty) {
      assert(m_domain_sizes.empty());
    }
    return is_empty;
  }

  void clear() noexcept
  {
    m_groups.clear();
    m_domain_sizes.clear();
    assert(empty());
  }

  void reserve(uint32_t var_count, uint32_t group_count)
  {
    m_groups.reserve(var_count);
    m_domain_sizes.reserve(group_count);
  }

  // Register a new (unassigned) variable with a group
  void set_group(Var v, Group g)
  {
    assert(v.is_valid());
    assert(g != InvalidGroup);
    while (v.index() >= m_groups.size()) {
      m_groups.push_back(InvalidGroup);
    }
    while (g >= m_domain_sizes.size()) {
      m_domain_sizes.push_back(0);
    }
    assert(m_groups[v] == InvalidGroup);  // the group should be set only once, otherwise we have to correctly de-register from previous group
    m_groups[v] = g;
    m_domain_sizes[g] += 1;
    LOG_DEBUG("Adding variable " << v << " to group " << g << ", domain size now is " << m_domain_sizes[g]);
  }

  void assigned(Var v)
  {
    if (v.index() < m_groups.size()) {  // TODO: for subsumption problems, can convert this into an assertion
      Group g = m_groups[v];
      if (g != InvalidGroup) {
        m_domain_sizes[g] -= 1;
        LOG_DEBUG("Assigned variable " << v << " of group " << g << ", domain size now is " << m_domain_sizes[g]);
      }
    }
  }

  void unassigned(Var v)
  {
    if (v.index() < m_groups.size()) {  // TODO: for subsumption problems, can convert this into an assertion
      Group g = m_groups[v];
      if (g != InvalidGroup) {
        m_domain_sizes[g] += 1;
        LOG_DEBUG("Unassigned variable " << v << " of group " << g << ", domain size now is " << m_domain_sizes[g]);
      }
    }
  }

  /// Select variable with the smallest non-zero domain size.
  template <typename A>
  Var select_min_domain(vector_map<Lit, Value, A> const& values)
  {
    // TODO: for now, we just do a simple linear search
    //       a smarter algorithm could mark the whole group as inactive as soon as one variable from it is assigned to TRUE (the others will be immediately propagated false by the theory propagator).
    // TODO: for now, we choose the first unassigned variable from the group. Maybe we should choose the most "recent" one (recent in the VMTF sense), or something else?
    // Find group with minimal non-zero size
    Group sg = InvalidGroup;
    GroupSize sg_size = std::numeric_limits<uint32_t>::max();
    for (Group g = 0; g < m_domain_sizes.size(); ++g) {
      GroupSize const g_size = m_domain_sizes[g];
      if (0 < g_size && g_size < sg_size) {
        sg = g;
        sg_size = g_size;
      }
    }
    // Find an unassigned variable from that group, we simply return the first one.
    for (Var::index_type idx = 0; idx < m_groups.size(); ++idx) {
      Var v{idx};
      if (m_groups[v] == sg && values[v] == Value::Unassigned) {
        LOG_INFO("Domain degree: choose variable " << v << " of group " << sg << " with size " << sg_size);
        return v;
      }
    }
    // This will only be reached if all variables are assigned, but then we don't make a decision.
    LOG_INFO("Domain degree: no valid choice");
    return Var::invalid();
  }

private:
  // TODO: rename to m_var_groups?
  vector_map<Var, Group, allocator_type<Group>> m_groups;
  // TODO: rename to m_group_sizes?
  vector_map<Group, GroupSize, allocator_type<GroupSize>> m_domain_sizes;  ///< the number of unassigned variables belonging to each group
};


}  // namespace subsat

#endif /* !DOMAIN_DEGREE_HPP */
