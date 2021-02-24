#ifndef SUBSTITUTIONTHEORY2_HPP
#define SUBSTITUTIONTHEORY2_HPP

#include "SMTSubsumption/MapBinder.hpp"
#include "Kernel/Term.hpp"
#include "Lib/STL.hpp"
#include "SMTSubsumption/minisat/SolverTypes.h"

#include <algorithm>
#include <type_traits>

#include "SMTSubsumption/cdebug.hpp"

#include "./subsat/vector_map.hpp"
#include "./subsat/types.hpp"


namespace SMTSubsumption {

using namespace Kernel;


template <template <typename> class Allocator = std::allocator>
class SubstitutionTheory2 final {
public:
  /// Domain of the substitution: Vampire's FOL variables
  using VampireVar = unsigned int;

  /// Range of the substitution: Vampire's FOL terms
  // using range = TermList;

  template <typename T>
  using allocator_type = Allocator<T>;

  template <typename T>
  using vector = std::vector<T, allocator_type<T>>;

  template <typename K, typename T>
  using vector_map = subsat::vector_map<K, T, allocator_type<T>>;

public:
  // empty substitution theory
  SubstitutionTheory2()
  {
    m_bindings.reserve(32);
    m_bindings_storage.reserve(128);
  }

  // prevent accidental copies
  SubstitutionTheory2(SubstitutionTheory2& other) = delete;
  SubstitutionTheory2& operator=(SubstitutionTheory2& other) = delete;

  // but we allow moves
  SubstitutionTheory2(SubstitutionTheory2&& other) = default;
  SubstitutionTheory2& operator=(SubstitutionTheory2&& other) = default;

public:
  using BindingsEntry = std::pair<VampireVar, TermList>;
  using BindingsStorage = vector<BindingsEntry>;

  class Binder {
  public:
    Binder(BindingsStorage& bindings_storage) noexcept
        : m_bindings_storage{bindings_storage}
        , m_bindings_start{bindings_storage.size()}
    { }

    Binder(Binder&) = delete;
    Binder& operator=(Binder&) = delete;
    Binder(Binder&&) = default;
    Binder& operator=(Binder&&) = delete;

    bool bind(VampireVar var, TermList term)
    {
      // // Try to find entry for 'var'
      // auto it =
      //     std::find_if(m_bindings_storage.begin() + m_bindings_start, m_bindings_storage.end(),
      //                  [var](BindingsEntry entry) { return entry.first == var; });
      // if (it != m_bindings_storage.end()) {
      //   // 'var' is already bound => successful iff we bind to the same term again
      //   return it->second == term;
      // }
      // else {
      //   // 'var' is not bound yet => store new binding
      //   m_bindings_storage.emplace_back(var, term);
      //   return true;
      // }
      for (auto it = m_bindings_storage.cbegin() + m_bindings_start; it != m_bindings_storage.cend(); ++it) {
        if (it->first == var) {
          // 'var' is already bound => successful iff we bind to the same term again
          return (it->second == term);
        }
      }
      // 'var' is not bound yet => store new binding
      m_bindings_storage.emplace_back(var, term);
      return true;
    }

    void specVar(VampireVar var, TermList term)
    {
      ASSERTION_VIOLATION;
    }

    void reset()
    {
      ASS_GE(m_bindings_storage.size(), m_bindings_start);
      m_bindings_storage.resize(m_bindings_start);
    }

    size_t index() const noexcept
    {
      return m_bindings_start;
    }

    size_t size() const noexcept
    {
      ASS_GE(m_bindings_storage.size(), m_bindings_start);
      return m_bindings_storage.size() - m_bindings_start;
    }

  private:
    BindingsStorage& m_bindings_storage;
    /// First index of the current bindings in m_bindings_storage
    size_t m_bindings_start;
  };  // class Binder

  /// Only one binder may be active at any time.
  /// Must call register_bindings or drop_bindings on the returned binder.
  Binder start_binder() noexcept
  {
    return {m_bindings_storage};
  }

  void register_bindings(subsat::Var b, Binder&& binder)
  {
    while (b.index() >= m_bindings.size()) {
      m_bindings.emplace_back();
    }
    BindingsRef& bindings = m_bindings[b];
    ASS(!bindings.is_valid());
    bindings.index = binder.index();
    bindings.size = binder.size();

    for (uint32_t i = bindings.index; i < bindings.end(); ++i) {
      BindingsEntry const& entry = m_bindings_storage[i];
      VampireVar var = entry.first;
      TermList term = entry.second;
      while (var >= m_bindings_by_var.size()) {
        m_bindings_by_var.emplace_back();
      }
      auto& var_bindings = m_bindings_by_var[var];
      if (var_bindings.empty()) {
        m_used_vars.push_back(var);
      }
      var_bindings.emplace_back(var, term);
    }
  }

  void drop_bindings(Binder&& binder)
  {
    binder.reset();
  }

private:
  struct BindingsRef {
    uint32_t index = std::numeric_limits<uint32_t>::max();
    uint32_t size = 0;

    constexpr bool is_valid() const
    {
      return index < std::numeric_limits<uint32_t>::max();
    }
    /// last index + 1
    uint32_t end()
    {
      return index + size;
    }
  };

public:
  void clear() noexcept
  {
    m_bindings_storage.clear();
    m_bindings.clear();
    for (VampireVar v : m_used_vars) {
      m_bindings_by_var.clear();
    }
    m_used_vars.clear();
  }

  bool empty() const noexcept
  {
    bool is_empty = m_bindings_storage.empty();
    if (is_empty) {
      ASS(m_bindings.empty());
      ASS(m_used_vars.empty());
      for (auto const& vec : m_bindings_by_var) {
        ASS(vec.empty());
      }
    }
    return is_empty;
  }

public:
    /// Call this when a SAT variable has been set to true
    /// PropagateCallback ~ bool propagate(subsat::Lit propagated, Lit reason)
    template < typename PropagateCallback >
    bool enable(subsat::Var b, PropagateCallback propagate)
    {
      // Retrieve the bindings corresponding to the given boolean variable
      BindingsRef bindings = m_bindings[b];

      // Exhaustively propagate the conflicting atoms
      for (uint32_t i = bindings.index; i < bindings.end(); ++i) {
        // Substitution constraint (X0 -> t) for b
        BindingsEntry entry = m_bindings_storage[i];
        // Go through possible other mappings for X0
        for (auto q : m_bindings_by_var[entry.first]) {
          if (q.second != entry.second) {
            // conflicting substitution constraints
            subsat::Var conflicting_var = q.first;  // conflicting variable
            subsat::Lit reason = b;
            if (!propagate(~conflicting_var, b)) {
              return false;
            }
          }
        }
      }
      return true;
    }  // enable(...)

private:
  BindingsStorage m_bindings_storage;

  vector_map<subsat::Var, BindingsRef> m_bindings;

  // Unfortunately vampire variables don't need to be contiguous
  vector<VampireVar> m_used_vars;
  vector_map<VampireVar, vector<std::pair<subsat::Var, TermList>>> m_bindings_by_var;
};


}  // namespace SMTSubsumption

#endif /* !SUBSTITUTIONTHEORY2_HPP */
