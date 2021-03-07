#ifndef SUBSTITUTIONTHEORY2_HPP
#define SUBSTITUTIONTHEORY2_HPP

#include <algorithm>
#include <type_traits>

#include "./subsat/vector_map.hpp"
#include "./subsat/types.hpp"
#include "./subsat/log.hpp"

#ifndef SUBSAT_STANDALONE
#include "Kernel/Term.hpp"
#endif


namespace SMTSubsumption {


/// Domain of the substitution: Vampire's FOL variables
using VampireVar = unsigned int;


#ifndef SUBSAT_STANDALONE

/// Range of the substitution: Vampire's FOL terms
using VampireTerm = ::Kernel::TermList;
#define SHOWVAR(var) (VampireTerm{var, false})
#define SHOWTERM(term) (term.toString())

#else

using VampireTerm = std::uint64_t;
#define ASSERTION_VIOLATION assert(false)
#define ASS(x) assert(x)
#define ASS_EQ(x, y) assert(x == y)
#define ASS_GE(x, y) assert(x >= y)
#define SHOWVAR(var) (var)
#define SHOWTERM(term) (term)

#endif  // !SUBSAT_STANDALONE

static_assert(sizeof(VampireTerm) == 8, "unexpected term size");


template <template <typename> class Allocator = std::allocator>
class SubstitutionTheory2 final {
public:

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
  using BindingsEntry = std::pair<VampireVar, VampireTerm>;
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

    bool bind(VampireVar var, VampireTerm term)
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

    void specVar(VampireVar /* var */, VampireTerm /* term */)
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
    ASS(bindings.is_valid());

    for (uint32_t i = bindings.index; i < bindings.end(); ++i) {
      BindingsEntry const& entry = m_bindings_storage[i];
      VampireVar var = entry.first;
      VampireTerm term = entry.second;
      LOG_TRACE(SHOWVAR(var) << " -> " << SHOWTERM(term));
      while (var >= m_bindings_by_var.size()) {
        m_bindings_by_var.emplace_back();
      }
      auto& var_bindings = m_bindings_by_var[var];
      if (var_bindings.empty()) {
        m_used_vars.push_back(var);
      }
      var_bindings.push_back({b, term});
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
      m_bindings_by_var[v].clear();
    }
    m_used_vars.clear();
  }

  bool empty() const noexcept
  {
    bool is_empty = m_bindings.empty();
    if (is_empty) {
      ASS(m_bindings_storage.empty());
      ASS(m_used_vars.empty());
#if VDEBUG
      for (auto const& vec : m_bindings_by_var) {
        ASS(vec.empty());
      }
#endif
    }
    return is_empty;
  }

  void reserve(std::uint32_t bool_var_count, std::uint32_t bindings_per_bool_var, std::uint32_t vampire_var_count)
  {
    m_bindings_storage.reserve(bool_var_count * bindings_per_bool_var);
    m_bindings.reserve(bool_var_count);
    m_used_vars.reserve(vampire_var_count);
    m_bindings_by_var.reserve(4*vampire_var_count);
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
      for (std::uint32_t i = bindings.index; i < bindings.end(); ++i) {
        // Substitution constraint (X0 -> t) for b
        BindingsEntry entry = m_bindings_storage[i];
        // Go through possible other mappings for X0
        for (auto q : m_bindings_by_var[entry.first]) {
          if (q.second != entry.second) {
            // conflicting substitution constraints
            subsat::Var const conflicting_var = q.first;  // conflicting variable
            subsat::Lit const reason = ~b;
            if (!propagate(~conflicting_var, reason)) {
              return false;
            }
          }
        }
      }
      return true;
    }  // enable(...)

private:
  // TODO: bindings in the array could be stored in a heap structure (i.e., one heap per binder).
  // Then we don't need to do linear search.
  // Furthermore, one could use the heap structure only for terms with a large number of variables.
  BindingsStorage m_bindings_storage;

  vector_map<subsat::Var, BindingsRef> m_bindings;

  // TODO: instead of these bindings, just store a vector_map<subsat::Var, vector<subsat::Var>>
  // that lists for each boolean variable the list of propagations.
  // This list can be built lazily during solving. Need also a flag whether the vector is initialized.
  // combined: vector_map<subsat::Var, std::pair<bool, vector<subsat::Var>>> ??
  // separate:
  // vector_map<subsat::Var, char>
  // vector_map<subsat::Var, vector<subsat::Var>>
  //
  // Unfortunately vampire variables don't need to be contiguous
  vector<VampireVar> m_used_vars;
  vector_map<VampireVar, vector<std::pair<subsat::Var, VampireTerm>>> m_bindings_by_var;
  // TODO: build bindings_by_var at the start of solve().
  // do not theory-propagate during building the problem, but do an initial round at the start of solve
  // (where tprop may fail on lvl 0; it's fine because we can just report unsat then.)
};


}  // namespace SMTSubsumption

#endif /* !SUBSTITUTIONTHEORY2_HPP */
