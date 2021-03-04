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
    uint32_t sg_size = std::numeric_limits<uint32_t>::max();
    for (Group g = 0; g < m_domain_sizes.size(); ++g) {
      uint32_t const g_size = m_domain_sizes[g];
      if (0 < g_size && g_size < sg_size) {
        sg = g;
        sg_size = g_size;
      }
    }
    // Find an unassigned variable from that group, we simply return the first one.
    for (uint32_t v_idx = 0; v_idx < m_groups.size(); ++v_idx) {
      Var v{v_idx};
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
  vector_map<Var, Group, allocator_type<Group>> m_groups;
  vector_map<Group, uint32_t, allocator_type<uint32_t>> m_domain_sizes;  ///< the number of unassigned variables belonging to each group
};


}  // namespace subsat

#endif /* !DOMAIN_DEGREE_HPP */
