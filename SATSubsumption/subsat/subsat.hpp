#ifndef SUBSAT_HPP
#define SUBSAT_HPP

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <initializer_list>
#include <iterator>
#include <limits>
#include <new>
#include <ostream>
#include <iomanip>
#include <set>
#include <map>
#include <vector>

#include "./subsat_config.hpp"
#include "./constraint.hpp"
#include "./decision_queue.hpp"
#include "./variable_domain_size.hpp"
#include "./types.hpp"
#include "./vector_map.hpp"
#include "./log.hpp"
#include "./SubstitutionTheory.hpp"



namespace subsat {

std::ostream& print_config(std::ostream& os);

struct Statistics {
#if SUBSAT_LIMITS
  uint64_t ticks = 0;             ///< Number of ticks (an arbitrary but deterministic measure of time spent solving).
#endif
#if SUBSAT_STATISTICS
  int conflicts = 0;              ///< Number of conflicts encountered.
  int decisions = 0;              ///< Number of decisions.
  int propagations = 0;           ///< Number of unit propagations performed.
#if SUBSAT_STATISTICS >= 2
  int conflicts_by_amo = 0;       ///< Number of conflicts due to violated AtMostOne-constraint.
  int conflicts_by_clause = 0;    ///< Number of conflicts due to violated clause.
  int propagations_by_amo = 0;    ///< Number of unit propagations caused by AtMostOne-constraints.
  int propagations_by_clause = 0; ///< Number of unit propagations caused by clauses.
  int propagations_by_theory = 0; ///< Number of unit propagations caused by substitution theory.
  int learned_unit_clauses = 0;   ///< Number of learned unit clauses.
  int learned_binary_clauses = 0; ///< Number of learned binary clauses.
  int learned_long_clauses = 0;   ///< Number of learned long clauses (size >= 3).
  int learned_literals = 0;       ///< Sum of the sizes of all learned clauses.
#endif
  std::size_t max_stored_literals = 0;    ///< Maximum number of literals in the m_constraints storage.
#if SUBSAT_MINIMIZE && SUBSAT_STATISTICS >= 2
  int minimized_literals = 0;     ///< Number of literals removed by learned clause minimization.
#endif
  int original_clauses = 0;       ///< Total number of (non-unit) original clauses.
  int original_amos = 0;          ///< Total number of AtMostOne-constraints (proper AMO constraints, i.e., at least 3 literals).
#if SUBSAT_RESTART
  int restarts = 0;               ///< Number of restarts performed.
#endif
#endif  // SUBSAT_STATISTICS

  void reset() { *this = Statistics(); }
};

static inline std::ostream& operator<<(std::ostream& os, Statistics const& stats)
{
#if SUBSAT_STATISTICS
  os << subsat::string(70, '-') << '\n';
#if SUBSAT_RESTART
  os << "Restarts:         " << std::setw(8) << stats.restarts << '\n';
#endif
  os << "Decisions:        " << std::setw(8) << stats.decisions << '\n';
  os << "Propagations:     " << std::setw(8) << stats.propagations;
#if SUBSAT_STATISTICS >= 2
  os << " (by clause: " << stats.propagations_by_clause << ", by amo: " << stats.propagations_by_amo << ", by theory: " << stats.propagations_by_theory << ")";
#endif
  os << "\n";
  os << "Conflicts:        " << std::setw(8) << stats.conflicts;
#if SUBSAT_STATISTICS >= 2
  os << " (by clause: " << stats.conflicts_by_clause << ", by amo: " << stats.conflicts_by_amo << ")";
#endif
  os << "\n";
#if SUBSAT_STATISTICS >= 2
  auto const total_learned_clauses = stats.learned_long_clauses + stats.learned_binary_clauses + stats.learned_unit_clauses;  // same as #conflicts during solving since we don't delete any
  os << "Learned clauses:  " << std::setw(8) << total_learned_clauses << " (" << stats.learned_long_clauses << " long, " << stats.learned_binary_clauses << " binary, " << stats.learned_unit_clauses << " unit)\n";
  os << "Learned literals: " << std::setw(8) << stats.learned_literals << " (on average " << std::setprecision(1) << std::fixed << (static_cast<double>(stats.learned_literals) / total_learned_clauses) << " literals/clause)\n";
#endif
#if SUBSAT_MINIMIZE && SUBSAT_STATISTICS >= 2
  os << "Minimized literals:" << std::setw(7) << stats.minimized_literals << " (on average " << std::setprecision(1) << std::fixed << (static_cast<double>(stats.minimized_literals) / total_learned_clauses) << " literals/clause)\n";
#endif
  os << "Max. storage used:" << std::setw(8) << stats.max_stored_literals << " literals";
#if SUBSAT_STATISTICS >= 2
  os << " (= learned literals + clause headers + " << (stats.max_stored_literals - static_cast<std::size_t>(stats.learned_literals + stats.learned_long_clauses + stats.learned_binary_clauses)) << ")";
#endif
  os << "\n";
#if SUBSAT_STATISTICS >= 2
  assert(stats.conflicts == stats.conflicts_by_clause + stats.conflicts_by_amo);
  assert(stats.propagations == stats.propagations_by_clause + stats.propagations_by_amo + stats.propagations_by_theory);
#endif
#endif  // SUBSAT_STATISTICS
  return os;
}

#if SUBSAT_STATISTICS

#define SUBSAT_STAT_ADD(NAME, VALUE)                                                \
  do {                                                                              \
    auto v = static_cast<decltype(m_stats.NAME)>(VALUE);                            \
    assert(m_stats.NAME <= std::numeric_limits<decltype(m_stats.NAME)>::max() - v); \
    m_stats.NAME += v;                                                              \
  } while (false)

#define UPDATE_STORAGE_STATS()                                                                 \
  do {                                                                                         \
    m_stats.max_stored_literals = std::max(m_stats.max_stored_literals, m_constraints.size()); \
  } while (false)

#if SUBSAT_STATISTICS >= 2
#define SUBSAT_STAT2_ADD(NAME, VALUE) SUBSAT_STAT_ADD(NAME, VALUE)
#else
#define SUBSAT_STAT2_ADD(NAME, VALUE) \
  do {                                \
    /* do nothing */                  \
  } while (false)
#endif

#else

#define SUBSAT_STAT_ADD(NAME, VALUE) \
  do {                               \
    /* do nothing */                 \
  } while (false)

#define UPDATE_STORAGE_STATS() \
  do {                         \
    /* do nothing */           \
  } while (false)
#endif  // SUBSAT_STATISTICS

#define SUBSAT_STAT_INC(NAME)   SUBSAT_STAT_ADD(NAME, 1)
#define SUBSAT_STAT2_INC(NAME)  SUBSAT_STAT2_ADD(NAME, 1)



struct Limits {
#if SUBSAT_LIMITS
  uint64_t max_ticks = std::numeric_limits<uint64_t>::max();
#endif

  void reset() { *this = Limits(); }
};



// The following adapted from https://github.com/arminbiere/satch/blob/8afbc3540a4b4ca028ed47124e44dabff2bbefb4/satch.c#L4196C33-L4196C33
//
// Estimate the number of cache lines spanning the given array.
//
// We could use the numerical vales of the 'begin' and 'end' pointers of the
// array but that would make the code dependent on memory addresses which
// should be avoided.  Therefore we fall back to an estimation, which in
// essence assumes that the start address is cache-line-size aligned.
//
// Typical size of a cache line is 128 bytes, but even if your processor has
// less or more, this computation is anyhow just a rough estimate and by
// keeping it machine independent we also keep scheduling of for instance
// the focused and stable phases and thus the whole solver execution machine
// independent (does not vary for different cache-line size).

#define log2_bytes_per_cache_line   7
#define bytes_per_cache_line        (1u << log2_bytes_per_cache_line)

inline
size_t cache_lines_bytes(size_t const bytes)
{
  size_t const round = bytes_per_cache_line - 1;
  size_t const res = (bytes + round) >> log2_bytes_per_cache_line;
  return res;
}

inline
size_t cache_lines_array(void const* begin, void const* end)
{
  size_t const bytes = (char*)end - (char*)begin;
  return cache_lines_bytes(bytes);
}

template <typename T, typename Alloc>
size_t cache_lines_vec(std::vector<T, Alloc> const& vec)
{
  size_t const bytes = sizeof(T) * vec.size();
  return cache_lines_bytes(bytes);
}





using Level = uint32_t;
#define InvalidLevel (std::numeric_limits<Level>::max())


/// Represents the reason for assigning a variable.
/// Invariant: all literals (other than the implied one) are false.
class Reason final {
  enum class Type : uint8_t {
    Invalid,
    Binary,
    ClauseRef,
#if !SUBSAT_LEARN
    ClauseRefRedundant,
#endif
  };

  // TODO: could take away a bit from Lit/ConstraintRef to discriminate the union and get rid of the type field
  Type type = Type::Invalid;

  union {
    Lit binary_other_lit;
    ConstraintRef clause_ref;
  };

public:
  constexpr Reason() noexcept
    : type{Type::Invalid}
    , clause_ref{ConstraintRef::invalid()}
  { }

  explicit Reason(Lit other) noexcept
    : type{Type::Binary}
    , binary_other_lit{other}
  {
    assert(other.is_valid());
  }

  explicit Reason(ConstraintRef cr) noexcept
    : type{Type::ClauseRef}
    , clause_ref{cr}
  {
    assert(cr.is_valid());
  }

#if !SUBSAT_LEARN
  explicit Reason(ConstraintRef cr, bool redundant) noexcept
    : type{redundant ? Type::ClauseRefRedundant : Type::ClauseRef}
    , clause_ref{cr}
  {
    assert(cr.is_valid());
  }

  constexpr bool is_redundant() const noexcept
  {
    return type == Type::ClauseRefRedundant;
  }
#endif

  static constexpr Reason invalid() noexcept
  {
    return Reason();
  }

  constexpr bool is_valid() const noexcept
  {
    return type != Type::Invalid;
  }

  constexpr bool is_binary() const noexcept
  {
    return type == Type::Binary;
  }

  Lit get_binary_other_lit() const noexcept
  {
    assert(type == Type::Binary);
    return binary_other_lit;
  }

  ConstraintRef get_clause_ref() const noexcept
  {
#if SUBSAT_LEARN
    assert(type == Type::ClauseRef);
#else
    assert(type == Type::ClauseRef || type == Type::ClauseRefRedundant);
#endif
    return clause_ref;
  }
};
static_assert(std::is_trivially_destructible<Reason>::value, "");


struct VarInfo final {
  Level level = InvalidLevel;
  Reason reason;

  constexpr bool is_decision() const noexcept
  {
    return level > 0 && !reason.is_valid();
  }
};
static_assert(std::is_trivially_destructible<VarInfo>::value, "");


struct Watch final {
  constexpr Watch() noexcept
    : clause_ref{ConstraintRef::invalid()}
  { }

  constexpr Watch(ConstraintRef cr) noexcept
    : clause_ref{cr}
  { }

  // TODO: optimizations: blocking literal, virtual binary clauses
  //       (although kitten doesn't seem to do either of those)
  //       (note that neither of those will change setup costs since we already defer watchlist construction until solving starts)
  ConstraintRef clause_ref;
};
static_assert(std::is_trivially_destructible<Watch>::value, "");

/*
/// A watch stores a blocking literal and a reference to the constraint.
///
/// For virtual binary clauses (where binary clauses are only stored in the watchlists),
/// the binary clause's other literal is the blocking literal while the
/// cosntraint reference will be an invalid reference.
class Watch final {
#if SUBSAT_BLOCKING
  Lit blocking_lit = Lit::invalid();
#endif
  ConstraintRef constraint;

  constexpr Watch(Lit blocking, ConstraintRef c) noexcept
    : blocking_lit{blocking}, constraint{c}
  { }

public:
#if SUBSAT_VIRTUAL
  bool is_binary() noexcept {
    return constraint.is_valid();
  }

  static Watch mk_binary(Lit other) noexcept {
    return Watch(other, ConstraintRef::invalid());
  }
#endif

  static Watch mk_long(Lit blocking, ConstraintRef c) noexcept {
    return Watch(blocking, c);
  }

#if SUBSAT_BLOCKING
  Lit get_blocking_lit() noexcept {
    return blocking_lit;
  }
#endif
};
static_assert(std::is_trivially_destructible<Watch>::value, "");
*/


using Mark = signed char;
enum : Mark {
  MarkSeen = 1,
#if SUBSAT_MINIMIZE
  MarkPoisoned = 2,
  MarkRemovable = 4,
#endif
};


#if SUBSAT_LOGGING_ENABLED
struct ShowConstraintRef {
  ShowConstraintRef(ConstraintArena const& arena, ConstraintRef cr) noexcept
    : arena(arena), cr(cr)
  { }
  ConstraintArena const& arena;
  ConstraintRef cr;
};

inline std::ostream& operator<<(std::ostream& os, ShowConstraintRef const& scr)
{
  if (scr.cr.is_valid()) {
    os << scr.arena.deref(scr.cr);
  } else {
    os << "{-}";
  }
  return os;
}

struct ShowReason {
  ShowReason(ConstraintArena const& arena, Reason r) noexcept
    : arena(arena), r(r)
  { }
  ConstraintArena const& arena;
  Reason r;
};

inline std::ostream& operator<<(std::ostream& os, ShowReason const& sr)
{
  Reason const& r = sr.r;
  if (r.is_valid()) {
    if (r.is_binary()) {
      os << r.get_binary_other_lit();
    } else {
      os << sr.arena.deref(r.get_clause_ref());
    }
  } else {
    os << "-";
  }
  return os;
}


struct ShowAssignment {
  ShowAssignment(Solver const& solver) : solver(solver) { }
  Solver const& solver;
};

std::ostream& operator<<(std::ostream& os, ShowAssignment sa);

#define SHOWREF(cr) (ShowConstraintRef{m_constraints, cr})
#define SHOWREASON(r) (ShowReason{m_constraints, r})
#define SHOWASSIGNMENT() (ShowAssignment{*this})

#endif



/// SAT solver especially for subsumption-type problems.
///
/// Native support for
/// - boolean variables and clauses,
/// - at-most-one constraints,
/// - substitution theory.
///
/// Based on two solvers by Armin Biere:
/// - satch, see https://github.com/arminbiere/satch
/// - kitten, which is part of kissat, see https://github.com/arminbiere/kissat
class Solver {

public:
  using SubstitutionTheory = subsat::SubstitutionTheory;
  using BindingsManager = typename SubstitutionTheory::BindingsManager;

  using vdom = VariableDomainSize;
  using vdom_group = typename vdom::Group;

  using State = Result;


  /// Returns the next unused variable.
  NODISCARD Var new_variable(vdom_group group = vdom::InvalidGroup)
  {
    LOG_TRACE("new_variable");
    assert(m_state == State::Unknown);
    // NOTE: most initialization is done at the time of solving.
    //       new_variable and add_clause(_unsafe) should be as lightweight as possible,
    //       to keep the overhead low for (relatively common) cases where we can bail out early.
    //       The actual initialization is done in prepare_to_solve().
    Var new_var = Var{m_used_vars++};
#if SUBSAT_VDOM
    m_vdom.ensure_var(new_var);
    if (group != vdom::InvalidGroup) {
      m_vdom.set_group(new_var, group);
    }
#else
    (void)group;  // suppress warning about unused parameter
#endif
    return new_var;
  }

  /// Reserve space for 'count' variables (in total),
  /// but does not actually enable the new variables in the solver.
  void reserve_variables(uint32_t count)
  {
    assert(m_state == State::Unknown);
    m_vars.reserve(count);
    m_marks.reserve(count);
    m_values.reserve(2 * count);
#if SUBSAT_VDOM
    m_vdom.reserve(count, count);
#endif
#if SUBSAT_VMTF
    m_queue.reserve(count);
#endif
    m_watches.reserve(2 * count);
    m_watches_amo.reserve(2 * count);
    m_trail.reserve(count);
    m_original_constraints.reserve(32);

    tmp_analyze_clause.reserve(8);
    tmp_analyze_blocks.reserve(8);
    tmp_analyze_seen.reserve(16);
    m_frames.reserve(count+1);
  }

  /// Reserve storage for 'count' literals (less will be available since clause header is stored in the same space)
  void reserve_clause_storage(uint32_t count)
  {
    m_constraints.reserve(count);
  }

  SubstitutionTheory& theory()
  {
    return m_theory;
  }

  Statistics const& stats()
  {
    return m_stats;
  }

  Limits const& limits()
  {
    return m_limits;
  }

#if SUBSAT_LIMITS
  // Set maximum number of ticks.
  void set_max_ticks(uint64_t max_ticks)
  {
    m_limits.max_ticks = max_ticks;
  }
#endif


  /// Return true iff the solver is empty
  /// (i.e., in the state after construction/clear).
  bool empty() const
  {
    bool const is_empty = (m_used_vars == 0);
    if (is_empty) { assert(checkEmpty()); }
    return is_empty;
  }


  /// Reset solver to empty state, but keep allocated memory buffers.
  void clear()
  {
    uint32_t const old_used_vars = m_used_vars;

    m_state = State::Unknown;
    m_inconsistent = false;
    m_used_vars = 0;
    m_unassigned_vars = 0;
    m_level = 0;

    m_values.clear();
    m_vars.clear();
    m_marks.clear();

#if SUBSAT_VDOM
    m_vdom.clear();
#endif
#if SUBSAT_VMTF
    m_queue.clear();
#endif

    m_constraints.clear();
    tmp_propagate_binary_conflict_ref = ConstraintRef::invalid();
#ifndef NDEBUG
    m_clause_refs.clear();
    m_atmostone_constraint_refs.clear();
#endif
    m_original_constraints.clear();

    // Don't clear m_watches itself! We want to keep the nested vectors to save re-allocations.
    assert(m_watches.size() == m_watches_amo.size());
    uint32_t const used_watches = std::min(2 * old_used_vars, static_cast<uint32_t>(m_watches.size()));
    for (uint32_t i = 0; i < used_watches; ++i) {
      m_watches[Lit::from_index(i)].clear();
      m_watches_amo[Lit::from_index(i)].clear();
    }

    m_trail.clear();
    m_propagate_head = 0;
    m_theory_propagate_head = 0;

    m_frames.clear();

    m_theory.clear();

    m_stats.reset();
    m_limits.reset();

    assert(checkEmpty());
  }

  /// Reset the constraint database, but keep the variables and theories.
  /// Also keeps the allocated memory buffers.
  void clear_constraints()
  {
    uint32_t const old_used_vars = m_used_vars;

    m_state = State::Unknown;
    m_inconsistent = false;
    m_unassigned_vars = m_used_vars;
    m_level = 0;

    m_values.clear();

#if SUBSAT_VDOM
    m_vdom.clear_domain_sizes();
#endif
#if SUBSAT_VMTF
    m_queue.clear();
#endif

    m_constraints.clear();
    tmp_propagate_binary_conflict_ref = ConstraintRef::invalid();
#ifndef NDEBUG
    m_clause_refs.clear();
    m_atmostone_constraint_refs.clear();
#endif
    m_original_constraints.clear();

    // Don't clear m_watches itself! We want to keep the nested vectors to save re-allocations.
    assert(m_watches.size() == m_watches_amo.size());
    uint32_t const used_watches = std::min(2 * old_used_vars, static_cast<uint32_t>(m_watches.size()));
    for (uint32_t i = 0; i < used_watches; ++i) {
      m_watches[Lit::from_index(i)].clear();
      m_watches_amo[Lit::from_index(i)].clear();
    }

    m_trail.clear();
    m_propagate_head = 0;
    m_theory_propagate_head = 0;

    m_frames.clear();

    m_stats.reset();
    m_limits.reset();
  }


  /********************************************************************
   * Creating new constraints
   ********************************************************************/

public:

  /// Opaque handle to fully-constructed constraints.
  class ConstraintHandle final {
    ConstraintHandle(ConstraintRef ref) : m_ref{ref} { }
    ConstraintRef m_ref;
    friend class Solver;
  };

  /// Reserve space for a constraint of at most 'capacity' literals
  /// and returns a handle to the storage.
  ///
  /// Call 'handle_push_literal' up to 'capacity' times to add literals to the constraint,
  /// and finish it with 'handle_build'.
  ///
  /// May not be called while a constraint started by 'constraint_start' is active!
  NODISCARD AllocatedConstraintHandle alloc_constraint(uint32_t capacity)
  {
    LOG_TRACE("alloc_constraint: " << capacity);
    auto handle = m_constraints.alloc(capacity);
    UPDATE_STORAGE_STATS();
    return handle;
  }

  /// Adds a literal to a pre-allocated constraint.
  void handle_push_literal(AllocatedConstraintHandle& handle, Lit lit) noexcept
  {
    m_constraints.handle_push_literal(handle, lit);
  }

  /// Finish a pre-allocated constraint.
  /// Call 'add_clause' to add it to the solver as a clause.
  ConstraintHandle handle_build(AllocatedConstraintHandle& handle) noexcept
  {
    return {m_constraints.handle_build(handle)};
  }

  /// Start a new constraint.
  /// Call 'constraint_push_literal' to add an arbitrary number of literals, and finish with 'constraint_end'.
  /// This method is useful when the size is not known a priori.
  /// Drawback: only one such constraint may be active at one time.
  void constraint_start()
  {
    m_constraints.start();
  }

  /// Add a literal to the constraint started by 'constraint_start'.
  void constraint_push_literal(Lit lit)
  {
    m_constraints.push_literal(lit);
  }

  /// Finish the constraint started by 'constraint_start' and returns a handle to it.
  /// Call 'add_clause' to add it to the solver as a clause.
  NODISCARD ConstraintHandle constraint_end() noexcept
  {
    UPDATE_STORAGE_STATS();
    return {m_constraints.end()};
  }


  /********************************************************************
   * Adding constraints to the solver
   ********************************************************************/

public:

  /// Add constraint by copying the given literals (convenience method)
  void add_constraint(Constraint::Kind kind, std::initializer_list<Lit> literals)
  {
    assert(m_state == State::Unknown);
    assert(literals.size() <= std::numeric_limits<uint32_t>::max());
    auto literals_size = static_cast<uint32_t>(literals.size());
    add_constraint(kind, literals.begin(), literals_size);
  }

  /// Add constraint by copying the given literals (convenience method)
  void add_constraint(Constraint::Kind kind, Lit const* literals, uint32_t count)
  {
    assert(m_state == State::Unknown);
    auto alloc_handle = alloc_constraint(count);
    for (Lit const* p = literals; p < literals + count; ++p) {
      handle_push_literal(alloc_handle, *p);
    }
    auto built_handle = handle_build(alloc_handle);
    add_constraint(kind, built_handle);
  }

  /// Add constraint to the solver.
  void add_constraint(Constraint::Kind kind, ConstraintHandle& handle)
  {
    assert(m_state == State::Unknown);
    ConstraintRef const cr = handle.m_ref;
    Constraint const& c = m_constraints.deref(cr);
    for (Lit lit : c) {
      assert(lit.is_valid());
      while (lit.var().index() >= m_used_vars) {
        (void)new_variable();
      }
    }
    add_constraint_unsafe(kind, handle);
  }

  /// Add constraint to the solver.
  /// Precondition: all variables in the clause have already been added to the solver.
  void add_constraint_unsafe(Constraint::Kind kind, ConstraintHandle& handle)
  {
    assert(m_state == State::Unknown);
    ConstraintRef const cr = handle.m_ref;
#ifndef NDEBUG
    Constraint const& c = m_constraints.deref(cr);
    assert(std::all_of(c.begin(), c.end(), [this](Lit lit){ return lit.var().index() < m_used_vars; }));
#endif
    if (kind == Constraint::Kind::Clause) { SUBSAT_STAT_INC(original_clauses); }
    if (kind == Constraint::Kind::AtMostOne) { SUBSAT_STAT_INC(original_amos); }
    m_original_constraints.push_back({kind, cr});
  }


  /********************************************************************
   * Convenience methods for adding clauses
   ********************************************************************/

  /// Add clause by copying the given literals (convenience method)
  void add_clause(std::initializer_list<Lit> literals) { add_constraint(Constraint::Kind::Clause, literals); }

  /// Add clause by copying the given literals (convenience method)
  void add_clause(Lit const* literals, uint32_t count) { add_constraint(Constraint::Kind::Clause, literals, count); }

  /// Add a constraint to the solver as a clause.
  void add_clause(ConstraintHandle& handle) { add_constraint(Constraint::Kind::Clause, handle); }

  /// Add a constraint to the solver as a clause.
  /// Precondition: all variables in the clause have already been added to the solver.
  void add_clause_unsafe(ConstraintHandle& handle) { add_constraint_unsafe(Constraint::Kind::Clause, handle); }


  /********************************************************************
   * Convenience methods for AtMostOne constraints
   ********************************************************************/

  /// Add an AtMostOne constraint by copying the given literals (convenience method)
  void add_atmostone_constraint(std::initializer_list<Lit> literals) { add_constraint(Constraint::Kind::AtMostOne, literals); }

  /// Add an AtMostOne constraint by copying the given literals (convenience method)
  void add_atmostone_constraint(Lit const* literals, uint32_t count) { add_constraint(Constraint::Kind::AtMostOne, literals, count); }

  /// Add an AtMostOne constraint to the solver.
  void add_atmostone_constraint(ConstraintHandle& handle) { add_constraint(Constraint::Kind::AtMostOne, handle); }

  /// Add an AtMostOne constraint to the solver.
  /// Precondition: all variables in the clause have already been added to the solver.
  void add_atmostone_constraint_unsafe(ConstraintHandle& handle) { add_constraint_unsafe(Constraint::Kind::AtMostOne, handle); }


  /********************************************************************
   * Simplifying clauses and adding them to internal data structures
   ********************************************************************/

private:
#if SUBSAT_SIMPLIFY_CLAUSES
#ifndef NDEBUG
  /// Returns true if the given clause cannot be simplified further,
  /// that is, all of the following conditions hold:
  /// 1. it is not a tautology,
  /// 2. it does not contain duplicate literals, and
  /// 3. none of its literals are assigned at the root level.
  bool isClauseSimplified(Constraint const& c)
  {
    set<Lit> lits;
    for (Lit lit : c) {
      assert(lit.var().index() < m_used_vars);
      if (lits.find(~lit) != lits.end()) {
        // Clause contains complementary literals => tautology
        return false;
      }
      bool inserted = lits.insert(lit).second;
      if (!inserted) {
        // Clause contains duplicate literals
        return false;
      }
      Value const lit_value = m_values[lit];
      if (lit_value != Value::Unassigned && get_level(lit) == 0) {
        // Clause contains fixed literal
        return false;
      }
    }
    return true;
  }
#endif

  /// Simplifies the given clause:
  /// 1. Skip tautologies and clauses that are already satisfied on the root level,
  /// 2. Remove duplicate literals and literals that are already false on the root level.
  ///
  /// Calling this method is only allowed at level 0, for two reasons:
  /// 1. we only need to do this for original clauses (learned clauses are already simplified),
  /// 2. we don't have to check levels of assigned variables during simplification.
  ///
  /// Returns true if the clause is a tautology or already satisfied at the root level,
  /// i.e., if we should skip it instead of adding it to the solver.
  bool simplifyClause(Constraint& c)
  {
    assert(m_level == 0);
    assert(std::all_of(m_marks.begin(), m_marks.end(), [](Mark m) { return m == 0; }));
    bool is_trivial = false;
    uint32_t i = 0;  // read iterator
    uint32_t j = 0;  // write iterator (will lag behind i if any literals have been removed)
    while (i < c.size()) {
      Lit const lit = c[i];
      Var const var = lit.var();
      assert(var.index() < m_used_vars);

      // copy literal by default
      c[j++] = c[i++];
      assert(j <= i);

      Value const lit_value = m_values[lit];
      if (lit_value == Value::True) {
        LOG_INFO("Clause satisfied on root level due to literal: " << lit);
        assert(get_level(var) == 0);
        is_trivial = true;
        break;
      }
      else if (lit_value == Value::False) {
        LOG_INFO("Literal false on root level: " << lit);
        assert(get_level(var) == 0);
        j--;  // remove literal
      }
      else {
        assert(lit_value == Value::Unassigned);
        Mark const prev_mark = m_marks[var];
        Mark const lit_mark = lit.is_positive() ? 1 : -1;
        if (prev_mark == 0) {
          m_marks[var] = lit_mark;
        }
        else if (prev_mark == lit_mark) {
          LOG_INFO("Removing duplicate literal " << lit);
          j--;  // remove literal
        }
        else {
          assert(prev_mark == -lit_mark);
          LOG_INFO("Clause is a tautology due to variable " << var);
          is_trivial = true;
          break;
        }
      }
    }
    assert(j <= c.m_size);
    c.m_size = j;
    // Reset marks
    for (Lit lit : c) {
      m_marks[lit.var()] = 0;
    }
    assert(std::all_of(m_marks.begin(), m_marks.end(), [](Mark m) { return m == 0; }));
    return is_trivial;
  }
#endif  // SUBSAT_SIMPLIFY_CLAUSES

  /// Simplify the given clause and insert it into the internal data structures.
  void simplify_and_connect_clause(ConstraintRef cr)
  {
    LOG_INFO("New original clause " << SHOWREF(cr));
    assert(m_state == State::Unknown);
    assert(m_level == 0);
    Constraint& c = m_constraints.deref(cr);

#if SUBSAT_SIMPLIFY_CLAUSES
    bool is_trivial = simplifyClause(c);
    if (is_trivial) {
      LOG_DEBUG("Skipping clause.");
      return; // skip clause
    }
    LOG_INFO("Adding simplified clause " << c);
    assert(isClauseSimplified(c));
#endif

    if (c.size() == 0) {
      // Empty clause means inconsistent
      m_inconsistent = true;
    }
    else if (c.size() == 1) {
      // Units are assigned directly
      Lit lit = c[0];
      assert(lit.var().index() < m_used_vars);
      switch (m_values[lit]) {
        case Value::True:
          LOG_INFO("Skipping redundant unit clause: " << lit);
          break;
        case Value::False:
          LOG_INFO("Inconsistent unit clause: " << lit);
          m_inconsistent = true;
          break;
        case Value::Unassigned:
          LOG_INFO("Adding unit clause: " << lit);
          basic_assign(lit, Reason::invalid());
          break;
      }
    }
    else {
      // Long clauses will be added to the watch lists
      // TODO: special handling for binary clauses
      assert(c.size() >= 2);
      connect_clause(cr);
    }
  }

  /// Insert the given clause into internal data structures.
  /// Precondition: size >= 2.
  void connect_clause(ConstraintRef cr)
  {
#ifndef NDEBUG
      m_clause_refs.push_back(cr);
#endif
      watch_clause(cr);
  }


  /********************************************************************
   * Simplifying AtMostOne constraints and adding them to internal data structures
   ********************************************************************/

private:
#if SUBSAT_SIMPLIFY_AMOS
#ifndef NDEBUG
  /// Returns true if the given AtMostOne constraint cannot be simplified further,
  /// that is, all of the following conditions hold:
  /// 1. it is not a tautology (i.e., its size is at least 2),
  /// 2. it does not contain duplicate literals, and
  /// 3. none of its literals are assigned at the root level.
  bool isAmoSimplified(Constraint const& c)
  {
    if (c.size() < 2) {
      // AMO is always satisfied
      return false;
    }
    set<Lit> lits;
    for (Lit lit : c) {
      assert(lit.var().index() < m_used_vars);
      if (lits.find(~lit) != lits.end()) {
        // AMO contains complementary literals
        // => either it is a tautology (when size 2), or we can propagate all other literals to false
        return false;
      }
      bool inserted = lits.insert(lit).second;
      if (!inserted) {
        // AMO contains duplicate literals
        return false;
      }
      Value const lit_value = m_values[lit];
      if (lit_value != Value::Unassigned && get_level(lit) == 0) {
        // AMO contains fixed literal
        return false;
      }
    }
    return true;
  }
#endif

  /// Simplifies the given AtMostOne constraint:
  /// 1. Skip tautologies and AMOs that are already satisfied on the root level,
  /// 2. Remove duplicate literals and literals that are already false on the root level.
  ///
  /// Calling this method is only allowed at level 0, for two reasons:
  /// 1. we only need to do this for original AMOs once before they are added, and
  /// 2. we don't have to check levels of assigned variables during simplification.
  ///
  /// Returns true if the AtMostOne constraint is trivial,
  /// i.e., if we should skip it instead of adding it to the solver.
  bool simplifyAmo(Constraint& c)
  {
    assert(m_level == 0);
    assert(std::all_of(m_marks.begin(), m_marks.end(), [](Mark m) { return m == 0; }));
    if (c.size() < 2) {
      // always satisfied
      return true;
    }
    bool is_trivial = false;
    uint32_t i = 0;  // read iterator
    uint32_t j = 0;  // write iterator (will lag behind i if any literals have been removed)
    while (i < c.size()) {
      Lit const lit = c[i];
      Var const var = lit.var();
      assert(var.index() < m_used_vars);

      // copy literal by default
      c[j++] = c[i++];
      assert(j <= i);

      Value const lit_value = m_values[lit];
      if (lit_value == Value::True) {
        LOG_INFO("AtMostOne constraint has true literal on root level: " << lit);
        assert(get_level(var) == 0);
        // One literal of the AMO is already true => propagate all others to be false
        for (uint32_t k = 0; k < c.size(); ++k) {
          Lit const other = c[k];
          if (other == lit) {
            continue;
          }
          if (m_values[other] == Value::True) {
            // conflict at root level!
            LOG_INFO("AtMostOne constraint is conflicting on root level due to literals: " << lit << ", " << other);
            m_inconsistent = true;
            break;
          }
          else if (m_values[other] == Value::Unassigned) {
            // propagate other literal to false
            basic_assign(~other, Reason::invalid());
          }
          else {
            assert(m_values[other] == Value::False);
            // other literal already false => nothing to do
          }
        }
        is_trivial = true;
        break;
      }
      else if (lit_value == Value::False) {
        LOG_INFO("Literal false on root level: " << lit);
        assert(get_level(var) == 0);
        j--;  // remove literal
      }
      else {
        assert(lit_value == Value::Unassigned);
        Mark const prev_mark = m_marks[var];
        Mark const lit_mark = lit.is_positive() ? 1 : -1;
        if (prev_mark == 0) {
          m_marks[var] = lit_mark;
        }
        else if (prev_mark == lit_mark) {
          LOG_INFO("Removing duplicate literal " << lit);
          j--;  // remove literal
        }
        else {
          assert(prev_mark == -lit_mark);
          LOG_INFO("AtMostOne constraint contains both polarities of variable " << var);
          // For example: AtMostOne(x, ~x, y, z, ...)
          // In this case we can propagate all other literals to false.
          // If we don't get a conflict, the AMO then degenerates to a tautology AtMostOne(x, ~x).
          for (uint32_t k = 0; k < c.size(); ++k) {
            Lit const other = c[k];
            if (other.var() == var) {
              continue;
            }
            if (m_values[other] == Value::True) {
              // conflict at root level!
              LOG_INFO("AtMostOne constraint is conflicting on root level due to literals: " << lit << ", " << other);
              m_inconsistent = true;
              break;
            }
            else if (m_values[other] == Value::Unassigned) {
              // propagate other literal to false
              basic_assign(~other, Reason::invalid());
            }
            else {
              assert(m_values[other] == Value::False);
              // other literal already false => nothing to do
            }
          }
          is_trivial = true;
          break;
        }
      }
    }
    assert(j <= c.m_size);
    c.m_size = j;
    // AtMostOne constraints of sizes 0 and 1 are tautologies
    if (c.size() <= 1) {
      is_trivial = true;
    }
    // Reset marks
    for (Lit lit : c) {
      m_marks[lit.var()] = 0;
    }
    assert(std::all_of(m_marks.begin(), m_marks.end(), [](Mark m) { return m == 0; }));
    return is_trivial;
  }
#endif  // SUBSAT_SIMPLIFY_AMOS

  void simplify_and_connect_atmostone_constraint(ConstraintRef cr)
  {
    LOG_INFO("Connecting AtMostOne constraint " << SHOWREF(cr));
    assert(m_state == State::Unknown);
    assert(m_level == 0);
    Constraint& c = m_constraints.deref(cr);

#if SUBSAT_SIMPLIFY_AMOS
    bool is_trivial = simplifyAmo(c);
    if (is_trivial) {
      LOG_DEBUG("Skipping AtMostOne constraint.");
      return; // skip constraint
    }
    LOG_INFO("Adding simplified AtMostOne constraint " << c);
    assert(isAmoSimplified(c));
#endif

    if (c.size() <= 1) {
      // AtMostOne constraints of sizes 0 and 1 are tautologies => do nothing
    } else if (c.size() == 2) {
      // AtMostOne constraint of size 2 is a binary clause
      // AtMostOne(p, q) == ~p \/ ~q
      c[0] = ~c[0];
      c[1] = ~c[1];
      assert(!SUBSAT_SIMPLIFY_AMOS || isClauseSimplified(c));
      simplify_and_connect_clause(cr);
    } else {
      // Add proper AtMostOne constraint
      assert(c.size() >= 3);
#ifndef NDEBUG
      m_atmostone_constraint_refs.push_back(cr);
#endif
      watch_atmostone_constraint(cr);
    }
  }

public:
  /// Returns true iff the solver is in an inconsistent state.
  /// (may return true before calling solve if e.g. an empty clause is added.)
  bool inconsistent() const
  {
    return m_inconsistent;
  }

  /// Prepare internal data structures for solving.
  void prepare_for_solving()
  {
    assert(m_state == State::Unknown);
    assert(m_level == 0);

    assert(m_values.size() == 0);
    m_unassigned_vars = m_used_vars;
    m_vars.resize(m_used_vars);
    m_marks.resize(m_used_vars, 0);
    m_values.resize(2 * m_used_vars, Value::Unassigned);
    if (m_watches.size() < 2 * m_used_vars) {
      m_watches.resize(2 * m_used_vars);
    }
    if (m_watches_amo.size() < 2 * m_used_vars) {
      m_watches_amo.resize(2 * m_used_vars);
    }

#if SUBSAT_VDOM
    m_vdom.prepare_for_solving();
#endif
#if SUBSAT_VMTF
    m_queue.resize_and_init(m_used_vars);
    assert(m_queue.checkInvariants(m_values));
#endif

    m_trail.reserve(m_used_vars);

    for (auto p : m_original_constraints) {
      Constraint::Kind const kind = p.first;
      ConstraintRef cr = p.second;
      switch (kind) {
        case Constraint::Kind::Clause:
          simplify_and_connect_clause(cr);
          break;
        case Constraint::Kind::AtMostOne:
          simplify_and_connect_atmostone_constraint(cr);
          break;
      }
      if (m_inconsistent) {
        // If we're inconsistent there's no point in further adding constraints
        return;
      }
    }

    m_frames.resize(m_used_vars + 1, 0);

    if (!tmp_propagate_binary_conflict_ref.is_valid()) {
      auto ca = alloc_constraint(2);
      handle_push_literal(ca, Lit::invalid());
      handle_push_literal(ca, Lit::invalid());
      tmp_propagate_binary_conflict_ref = handle_build(ca).m_ref;
    }

    m_theory.prepare_for_solving();
    theory_propagate_initial();
  }

  Result solve()
  {
    assert(m_state == State::Unknown || m_state == State::Sat);
#if SUBSAT_STATISTICS
    LOG_INFO((m_state != State::Sat ? "Starting solving with " : "Resuming solving with ")
             << m_used_vars << " variables, "
             << m_stats.original_clauses << " clauses, "
             << m_stats.original_amos << " at-most-one constraints");
#endif

    // Initialize data structures if this is the first call to solve
    if (m_state == State::Unknown) {
      prepare_for_solving();
    }

    Result res = Result::Unknown;

    // Last solve() returned Sat, so prepare to find next model
    if (m_state == State::Sat) {
#if SUBSAT_RESTART
#warning "Model enumeration probably doesn't work with restarting at the moment!"
#endif
      // TODO: proper implementation later (for now, we only need this for debugging anyway)
      if (m_level == 0) {
        m_inconsistent = true;
      } else {
        // Build conflict clause from the current decisions.
        auto conflict = alloc_constraint(m_level);
        for (Lit lit : m_trail) {
          if (m_vars[lit.var()].is_decision()) {
            handle_push_literal(conflict, ~lit);
          }
        }
        ConstraintRef conflict_ref = handle_build(conflict).m_ref;
        if (!analyze(conflict_ref)) {
          res = Result::Unsat;
        }
      }
    }

    if (m_inconsistent) {
      res = Result::Unsat;
    }

#if SUBSAT_RESTART
    uint32_t restart_countdown = SUBSAT_RESTART_INTERVAL;
#endif

#ifdef SUBSAT_STATISTICS_INTERVAL
    uint32_t stats_countdown = 0;
#endif

    LOG_TRACE("Start solving loop");
    while (res == Result::Unknown) {
#ifdef SUBSAT_STATISTICS_INTERVAL
      if (stats_countdown-- == 0) {
        stats_countdown = SUBSAT_STATISTICS_INTERVAL;
        std::cerr << m_stats;
      }
#endif

#if SUBSAT_LIMITS
      if (m_stats.ticks > m_limits.max_ticks)
        break;
#endif

      ConstraintRef conflict = propagate();

      assert(checkInvariants());

#if SUBSAT_LIMITS
      if (m_stats.ticks > m_limits.max_ticks)
        break;
#endif

      if (conflict.is_valid()) {
        if (!analyze(conflict)) {
          res = Result::Unsat;
        }
#if SUBSAT_RESTART
        if (restart_countdown > 0) {
          restart_countdown--;
        }
#endif
      }
      else if (m_unassigned_vars == 0) {
        assert(checkModel());
        res = Result::Sat;
      }
#if SUBSAT_RESTART
      else if (m_level > 0 && restart_countdown == 0) {
        restart();
        restart_countdown = SUBSAT_RESTART_INTERVAL;
      }
#endif
      else {
        // TODO: switch mode? reduce clause db?
        decide();
      }
    }

#if SUBSAT_STATISTICS >= 2
    std::cerr << m_stats;
#endif
    m_state = res;
    return res;
  }

  /// Copy the currently true literals into the given vector.
  template < typename Alloc >
  void get_model(std::vector<Lit, Alloc>& model) const
  {
    assert(m_state == State::Sat);
    assert(m_unassigned_vars == 0);
    model.assign(m_trail.begin(), m_trail.end());
  }

  /// Return the current value of the given literal.
  Value get_value(Lit lit) const
  {
    assert(m_state == State::Sat);
    assert(m_unassigned_vars == 0);
    return m_values[lit];
  }

private:

  /// Set the literal to true.
  /// Precondition: literal is not assigned.
  void basic_assign(Lit lit, Reason reason)
  {
    LOG_DEBUG("Assigning " << lit << ", reason: " << SHOWREASON(reason) << ", level: " << m_level);

    // TODO: kitten does phase-saving as well

    // precondition: not assigned
    assert(m_values[lit] == Value::Unassigned);
    assert(m_values[~lit] == Value::Unassigned);

    // not assigned also means not on trail
    assert(std::find(m_trail.begin(), m_trail.end(), lit) == m_trail.end());
    assert(std::find(m_trail.begin(), m_trail.end(), ~lit) == m_trail.end());

    m_values[lit] = Value::True;
    m_values[~lit] = Value::False;

    Var const var = lit.var();
    m_vars[var].level = m_level;
    m_vars[var].reason = reason;

    m_trail.push_back(lit);

#if SUBSAT_VDOM
    m_vdom.assigned(var);
#endif

    assert(m_unassigned_vars > 0);
    m_unassigned_vars -= 1;
  }

  void assign(Lit lit, Reason reason)
  {
    basic_assign(lit, reason);
    theory_propagate();
  }

  /// Theory-propagation after all original clauses have been added.
  /// This is separate from 'theory_propagate' because at this point we may actually get conflicts.
  /// Since we are on level 0, such conflicts will immediately result in unsatisfiability.
  void theory_propagate_initial()
  {
    assert(m_level == 0);
    if (m_theory.empty()) {
      m_theory_propagate_head = static_cast<uint32_t>(m_trail.size());
      return;
    }
    while (m_theory_propagate_head < m_trail.size()) {
      Lit p = m_trail[m_theory_propagate_head++];
      LOG_DEBUG("Theory-propagating " << p);
      if (p.is_positive()) {
        bool enabled =
            m_theory.enable(p.var(), [this](subsat::Lit propagated, Lit reason) {
              Value value = m_values[propagated];
              if (value == Value::False) {
                LOG_DEBUG("Theory conflict: got " << propagated << " from theory which is already false!");
                m_inconsistent = true;
                return false;
              }
              LOG_DEBUG("Assigning " << propagated << " due to theory");
              if (value == Value::Unassigned) {
                SUBSAT_STAT_INC(propagations);
                SUBSAT_STAT2_INC(propagations_by_theory);
                basic_assign(propagated, Reason{reason});
              } else {
                assert(m_values[propagated] == Value::True);
              }
              return true;
            });
        if (!enabled) {
          return;
        }
      }
    }
  }

  void theory_propagate()
  {
    if (m_theory.empty()) {
      m_theory_propagate_head = static_cast<uint32_t>(m_trail.size());
      return;
    }
    // NOTE on why we do theory propagation as part of enqueue and not in the propagate() loop:
    // - we don't want to iterate through watchlists multiple times
    // - but if we handle the watch completely, we may get multiple enqueues, and these may already contain a theory conflict
    //   (unless our specific problem structure somehow prevents this -- but I don't see how it would; and relying on that seems fragile anyways)
    // - so we cannot simply choose in each iteration what we do,
    //   we need to theory-propagate after *each* call to enqueue
    // - Also note that we may already get a conflict on decision level 0 if we add two theory-conflicting unit clauses.
    assert(m_propagate_head <= m_theory_propagate_head);
    while (m_theory_propagate_head < m_trail.size()) {
      Lit p = m_trail[m_theory_propagate_head++];
      LOG_DEBUG("Theory-propagating " << p);
      if (p.is_positive()) {
        bool enabled =
            m_theory.enable(p.var(), [this](subsat::Lit propagated, Lit reason) {
              LOG_DEBUG("Assigning " << propagated << " due to theory");
              if (m_values[propagated] == Value::Unassigned) {
                SUBSAT_STAT_INC(propagations);
                SUBSAT_STAT2_INC(propagations_by_theory);
                basic_assign(propagated, Reason{reason});
              } else {
                assert(m_values[propagated] == Value::True);
              }
              return true;
            });
        assert(enabled);
        (void)enabled;  // suppress "unused variable" warning
      }
    }
  }

  /// Make a decision.
  void decide()
  {
    assert(m_unassigned_vars > 0);
    assert(!m_inconsistent);
    assert(m_level < m_used_vars);
    SUBSAT_STAT_INC(decisions);

    m_level += 1;

    Var var = Var::invalid();
#if SUBSAT_VDOM
    var = m_vdom.select_min_domain(m_values);
#endif
#if SUBSAT_VMTF
    if (!var.is_valid()) {
      assert(m_queue.checkInvariants(m_values));
      var = m_queue.next_unassigned_variable(m_values);
    }
#endif
    assert(var.is_valid());

    // TODO: phase saving (+ hints?)
    // for now, just use the positive phase always (works quite well for our type of problems, or at least much better than always-negative)
    Lit decision{var, true};
    LOG_INFO("Decision: " << decision);
    assign(decision, Reason::invalid());
  }


  /// Unit propagation.
  /// Returns the conflicting clause when a conflict is encountered,
  /// or an invalid ClauseRef if all unit clauses have been propagated without conflict.
  ConstraintRef propagate()
  {
    LOG_TRACE("propagate");
    assert(m_theory_propagate_head == m_trail.size());

    ConstraintRef conflict = ConstraintRef::invalid();
    uint64_t ticks = 0;

    while (!conflict.is_valid() && m_propagate_head < m_trail.size()) {
      Lit const lit = m_trail[m_propagate_head++];
      conflict = propagate_literal(lit, ticks);
    }

    m_stats.ticks += ticks;

    return conflict;
  }


  /// Unit propagation for 'lit' over AtMostOne constraints.
  ConstraintRef propagate_literal_in_amos(Lit const lit, uint64_t& ticks)
  {
    Lit const not_lit = ~lit;

    auto const& watches = m_watches_amo[lit];
    ticks += cache_lines_vec(watches);

    // There's no need to copy/modify any watches here,
    // because as soon as an AtMostOne constraint triggers,
    // all other literals will be set to false immediately.
    for (Watch const& watch : watches) {
      ConstraintRef const cr = watch.clause_ref;
      Constraint& c = m_constraints.deref(cr);
      ticks++;
      assert(c.size() >= 3);
      for (Lit other_lit : c) {
        if (lit == other_lit) {
          continue;
        }
        Value const other_value = m_values[other_lit];
        if (other_value == Value::Unassigned) {
          // propagate
          LOG_DEBUG("Assigning " << ~other_lit << " due to AtMostOne constraint " << SHOWREF(cr));
          SUBSAT_STAT_INC(propagations);
          SUBSAT_STAT2_INC(propagations_by_amo);
          ticks++;
          assign(~other_lit, Reason{not_lit});
        }
        else if (other_value == Value::True) {
          // at least two literals in the AtMostOne constraint are true => conflict
          LOG_TRACE("Current assignment: " << SHOWASSIGNMENT());
          LOG_DEBUG("Conflict with AtMostOne constraint " << SHOWREF(cr));
          SUBSAT_STAT2_INC(conflicts_by_amo);
          Constraint& tmp_binary_clause = m_constraints.deref(tmp_propagate_binary_conflict_ref);
          tmp_binary_clause[0] = not_lit;
          tmp_binary_clause[1] = ~other_lit;
          return tmp_propagate_binary_conflict_ref;
        }
        else {
          assert(other_value == Value::False);
          // nothing to do
        }
      }
    }

    return ConstraintRef::invalid();
  }  // propagate_literal_in_amos


  /// Unit propagation for 'lit' over clauses.
  ConstraintRef propagate_literal_in_clauses(Lit const lit, uint64_t& ticks)
  {
    Lit const not_lit = ~lit;
    ConstraintRef conflict = ConstraintRef::invalid();

    vector<Watch>& watches = m_watches[not_lit];

    auto q = watches.begin();   // points to updated watch, follows p
    auto p = watches.cbegin();  // points to currently processed watch

    ticks += cache_lines_vec(watches);

    while (!conflict.is_valid() && p != watches.cend()) {
      Watch const& watch = *p;
      *q++ = *p++;  // keep the watch by default

      // TODO: binary clause optimization
      // if (p->binary) {
      // ...
      // } else {
      // ... (current code here)
      // }

      // TODO: blocking literal optimization

      ConstraintRef const clause_ref = watch.clause_ref;
      Constraint& clause = m_constraints.deref(clause_ref);
      assert(clause.size() >= 2);

      // We mainly count accesses to large clauses, which
      // can amount to up to 80% of solving time.
      // See https://github.com/arminbiere/satch/blob/8afbc3540a4b4ca028ed47124e44dabff2bbefb4/satch.c#L4336
      ticks++;

      // The two watched literals of a clause are stored as the first two literals,
      // but we don't know which one is not_lit and which one is the other one.
      // We use this XOR trick to get other_lit without branching.
      assert(clause[0] == not_lit || clause[1] == not_lit);
      Lit const other_lit = Lit::from_index( clause[0].index() ^ clause[1].index() ^ not_lit.index() );
      Value const other_value = m_values[other_lit];

      // Note that other_lit may be different from the blocking literal,
      // so we must check its value here.
      if (other_value == Value::True) {
        // TODO: update blocking literal to other_lit
        continue;
      }

      // Normalize watched literal positions
      clause[0] = other_lit;
      clause[1] = not_lit;

      // Search for a replacement for not_lit, should be true or unassigned
      Lit replacement = Lit::invalid();
      Value replacement_value = Value::False;

      auto replacement_it = clause.begin() + 2;
      for (; replacement_it != clause.end(); ++replacement_it) {
        replacement = *replacement_it;
        replacement_value = m_values[replacement];
        if (replacement_value != Value::False) {
          break;
        }
      }

      if (replacement_value == Value::True) {
        // The replacement literal is true, so it's enough to update the blocking literal.
        // Since we entered this clause, this means the current blocking literal is not true, so this update is always beneficial.
        // TODO: update blocking literal to replacement
        // Since the 'replacement' is true, the clause is only relevant when 'replacement' is unassigned.
        // So if it was assigned in an earlier decision level, that is actually good.
      }
      else if (replacement_value == Value::Unassigned) {
        // The replacement literal is unassigned.
        // Unwatch not_lit
        --q;
        // Swap watched literal with its replacement
        clause[1] = replacement;
        *replacement_it = not_lit;
        // Watch the replacement literal
        watch_clause_literal(replacement, /* TODO: other_lit, */ clause_ref);
        ticks++;
      }
      else if (other_value != Value::Unassigned) {
        // All literals in the clause are false => conflict
        assert(other_value == Value::False);
        SUBSAT_STAT2_INC(conflicts_by_clause);
        conflict = clause_ref;
      }
      else {
        // All literals except other_lit are false => propagate
        assert(other_value == Value::Unassigned);
        LOG_TRACE("Assigning " << other_lit << " due to clause " << SHOWREF(clause_ref));
        SUBSAT_STAT_INC(propagations);
        SUBSAT_STAT2_INC(propagations_by_clause);
        assign(other_lit, Reason{clause_ref});
        ticks++;
      }
    }  // while

    // Copy remaining watches
    while (p != watches.cend()) {
      *q++ = *p++;
    }
    auto const remaining_watches = std::distance(watches.begin(), q);
    assert(remaining_watches >= 0);
    watches.resize(static_cast<std::size_t>(remaining_watches));
    assert(watches.end() == q);

    return conflict;
  }  // propagate_literal_in_clauses


  /// Unit propagation for the given literal.
  ConstraintRef propagate_literal(Lit const lit, uint64_t& ticks)
  {
    LOG_DEBUG("Propagating " << lit);
    assert(m_values[lit] == Value::True);

    ticks++;

    ConstraintRef conflict = ConstraintRef::invalid();

    if (!conflict.is_valid())
      conflict = propagate_literal_in_amos(lit, ticks);

    if (!conflict.is_valid())
      conflict = propagate_literal_in_clauses(lit, ticks);

    return conflict;
  }  // propagate_literal


  /// Watch literal 'lit' in the given clause.
  void watch_clause_literal(Lit lit, /* TODO: Lit blocking_lit, */ ConstraintRef clause_ref)
  {
    LOG_DEBUG("Watching " << lit << /* " blocked by " << blocking_lit << */ " in " << SHOWREF(clause_ref));
    auto& watches = m_watches[lit];
    assert(std::all_of(watches.cbegin(), watches.cend(), [=](Watch w){ return w.clause_ref != clause_ref; }));
    watches.push_back(Watch{clause_ref});
  }


  /// Watch the first two literals in the given clause.
  void watch_clause(ConstraintRef clause_ref)
  {
    Constraint const& clause = m_constraints.deref(clause_ref);
    assert(clause.size() >= 2);
    watch_clause_literal(clause[0], /* TODO: clause[1], */ clause_ref);
    watch_clause_literal(clause[1], /* TODO: clause[0], */ clause_ref);
  }


  /// Watch every literal in the AtMostOne constraint
  void watch_atmostone_constraint(ConstraintRef cr)
  {
    Constraint const& c = m_constraints.deref(cr);
    assert(c.size() >= 3);
    for (Lit lit : c) {
      auto& watches = m_watches_amo[lit];
      assert(std::all_of(watches.cbegin(), watches.cend(), [=](Watch w) { return w.clause_ref != cr; }));
      watches.push_back(Watch{cr});
    }
  }


  /// Analyze conflict, learn a clause, backjump.
  /// Returns true if the search should continue.
  NODISCARD bool analyze(ConstraintRef conflict_ref)
  {
    LOG_INFO("Conflict clause " << SHOWREF(conflict_ref) << " on level " << m_level);
    LOG_TRACE("Assignment: " << SHOWASSIGNMENT());
    assert(!m_inconsistent);
    assert(conflict_ref.is_valid());
    assert(checkInvariants());
    SUBSAT_STAT_INC(conflicts);

    Level const conflict_level = m_level;
    if (conflict_level == 0) {
      // Conflict on root level
      m_inconsistent = true;
      return false;
    }

    // These variables are morally local variables,
    // but we store them as class members to avoid allocation overhead.
    vector<Lit>& clause = tmp_analyze_clause;    // the learned clause
    vector<Level>& blocks = tmp_analyze_blocks;  // the analyzed decision levels
    vector<Var>& seen = tmp_analyze_seen;        // the analyzed variables
    vector_map<Level, uint8_t>& frames = m_frames;    // for each decision level, whether it has been analyzed
    assert(clause.empty());
    assert(blocks.empty());
    assert(seen.empty());
    assert(frames.size() >= conflict_level);
    assert(std::all_of(frames.cbegin(), frames.cend(), [](char x){ return x == 0; }));

    // Reserve space for the first UIP
    clause.push_back(Lit::invalid());

    // Iterator into the trail, indicating the next literal to resolve
    auto t = m_trail.cend();
    // The number of literals in the current clause that are on the highest decision level.
    // We need to resolve all of them away except one to reach a UIP.
    uint32_t unresolved_on_conflict_level = 0;
    // The literal we have just resolved away, or invalid in the first step
    Lit uip = Lit::invalid();
    // The reason of the resolved literal, or the conflict clause in the first step
    Constraint const* reason_ptr = &m_constraints.deref(conflict_ref);
    Constraint tmp_binary{2};  // a stack-allocated clause has space for two literals

    uint64_t ticks = 0;

    while (true) {
      assert(reason_ptr);
      LOG_TRACE("Reason: " << *reason_ptr << ", uip: " << uip << ", unresolved: " << unresolved_on_conflict_level);
      Constraint const& reason_clause = *reason_ptr;
      ticks++;

      // TODO: reason->used = true

      for (Lit const lit : reason_clause) {
        Var const var = lit.var();
        LOG_TRACE("  Checking literal " << lit << " (level: " << get_level(var) << ")");

        // Skip the resolved literal
        if (lit == uip) {
          assert(m_values[uip] == Value::True);
          continue;
        }

        Level const lit_level = get_level(var);
        if (lit_level == 0) {
          // Skip literals at level 0 since they are unconditionally false
          continue;
        }

        Mark const mark = m_marks[var];
        assert(mark == 0 || mark == MarkSeen);
        if (mark) {
          // Skip already-seen variables to prevent duplicates in the learned clause,
          // and to correctly count the unresolved variables on the conflict level
          continue;
        }
        m_marks[var] = MarkSeen;
        seen.push_back(var);

        assert(m_values[lit] == Value::False);
        if (lit_level < conflict_level) {
          if (!frames[lit_level]) {
            blocks.push_back(lit_level);
            frames[lit_level] = true;
          }
          clause.push_back(lit);
        } else {
          assert(lit_level == conflict_level);
          unresolved_on_conflict_level++;
        }

        LOG_TRACE("    blocks: " << ShowVec(blocks));
        LOG_TRACE("    unresolved: " << unresolved_on_conflict_level);
      }  // for (lit : reason)

      // Find next literal to resolve by going backward over the trail.
      // We skip over unseen literals here because those are unrelated to the current conflict
      // (think of unit propagation branching out in an interleaved way).
      do {
        assert(t > m_trail.cbegin());
        uip = *(--t);
      } while (!m_marks[uip.var()]);

      // We have resolved away one literal on the highest decision level
      assert(get_level(uip) == conflict_level);
      unresolved_on_conflict_level--;
      if (unresolved_on_conflict_level == 0) {
        // We would resolve away the last literal on the highest decision level
        // => we reached the first UIP
        break;
      }

      Reason const reason = m_vars[uip.var()].reason;
      reason_ptr = &get_reason(uip, reason, tmp_binary);
    }  // while(true)

    m_stats.ticks += ticks;

    // TODO: analyze loop is a bit simpler in kitten, maybe we can do that too?
    //       kitten does not use any blocks/frames (we use them for minimization though)

    assert(uip.is_valid());
    Lit const not_uip = ~uip;
    clause[0] = not_uip;
    LOG_TRACE("Learning clause: " << ShowVec(clause));

    assert(std::all_of(clause.begin(), clause.end(), [this](Lit lit) { return m_values[lit] == Value::False; }));

#if SUBSAT_MINIMIZE
    minimize_learned_clause();
    LOG_TRACE("Minimized clause: " << ShowVec(clause));
#endif

    // uint32_t const glue = blocks.size();

    // We backjump to the second-highest decision level in the conflict clause
    // (which is the highest level below the conflict level).
    Level jump_level = 0;
    for (Level lit_level : blocks) {
      frames[lit_level] = 0;
      if (lit_level != conflict_level && jump_level < lit_level) {
        jump_level = lit_level;
      }
    }
    blocks.clear();

    // TODO: update averages

    // TODO: sort analyzed vars by time stamp?
    for (Var var : seen) {
      assert(m_values[var] != Value::Unassigned);  // precondition of DecisionQueue::move_to_front
#if SUBSAT_VMTF
      m_queue.move_to_front(var);
#endif
      assert(m_marks[var]);
      m_marks[var] = 0;
    }
    seen.clear();
#if SUBSAT_VMTF
    assert(m_queue.checkInvariants(m_values));
#endif

    backtrack(jump_level);

    uint32_t const size = static_cast<uint32_t>(clause.size());
    assert(size > 0);
    if (size == 1) {
      // We learned a unit clause
      assert(jump_level == 0);
      LOG_INFO("Learned unit: " << not_uip);
      SUBSAT_STAT2_INC(learned_unit_clauses);
      SUBSAT_STAT2_ADD(learned_literals, 1);
      assign(not_uip, Reason::invalid());
    }
    // else if (size == 2) {
    //   // TODO: binary clause optimization
    // }
    else {
      assert(size > 1);
      assert(jump_level > 0);

      // First literal at jump level becomes the other watch.
      for (auto it = clause.begin() + 1; ; ++it) {
        assert(it != clause.end());
        Lit const lit = *it;
        assert(get_level(lit) <= jump_level);
        if (get_level(lit) == jump_level) {
          *it = clause[1];
          clause[1] = lit;
          break;
        }
      }

      auto learned = alloc_constraint(size);
      for (Lit learned_lit : clause) {
        handle_push_literal(learned, learned_lit);
      }
      ConstraintRef learned_ref = handle_build(learned).m_ref;
#if SUBSAT_LEARN
      LOG_INFO("Learned: size = " << size << ", literals = " << SHOWREF(learned_ref));
      if (size == 2) { SUBSAT_STAT2_INC(learned_binary_clauses); }  // TODO: move this when adding binary clause optimization
      if (size >= 3) { SUBSAT_STAT2_INC(learned_long_clauses); }
      SUBSAT_STAT2_ADD(learned_literals, size);
      // TODO: call new_redundant_clause
      connect_clause(learned_ref);
      Reason reason{learned_ref};
#else
#ifndef NDEBUG
      m_clause_refs.push_back(learned_ref);
#endif
      Reason reason{learned_ref, true};  // mark as redundant so we delete it on backtracking
#endif
      assign(not_uip, reason);
    }

    clause.clear();

    return true;
  }  // analyze

#if SUBSAT_MINIMIZE
  bool minimize_literal(Lit lit, uint32_t depth)
  {
    constexpr uint32_t max_depth = 100;
    Var const var = lit.var();
    Mark const mark = m_marks[var];
    if (mark & MarkPoisoned) {
      return false; // previously shown not to be removable
    }
    if (mark & MarkRemovable) {
      return true; // previously shown to be removable
    }
    if (depth > 0 && (mark & MarkSeen)) {
      // Analyzed and not at initial depth
      // Why? We call this for all other literals of the reason for the caller's literal.
      // If all reason literals have been analyzed, they are in the clause.
      // Resolving with the reason is self-subsuming, so we can remove the caller's literal.
      return true;
    }
    if (depth > max_depth) {
      // Limit recursion depth (due to limited stack size)
      LOG_WARN("reached max_depth");  // just to see whether we ever hit the limit
      return false;
    }
    assert(m_values[lit] == Value::False);
    Reason const reason = m_vars[var].reason;
    if (!reason.is_valid()) {
      return false;  // decision cannot be removed
    }
    Level const level = get_level(var);
    if (level == 0) {
      return true;  // root-level units can be removed
    }
    if (!m_frames[level]) {
      assert(depth > 0);
      // decision level of 'lit' not present in clause
      // => resolving with reason of the caller's literal is not self-subsuming (it would pull in 'lit')
      // => not removable
      LOG_WARN("decision level not pulled into clause");  // just to see how common this is
      return false;
    }

    // TODO: check out kissat's tail-recursive version for binary clauses
    Constraint tmp_binary{2};  // a stack-allocated clause has space for two literals
    Constraint const& reason_clause = get_reason(~lit, reason, tmp_binary);
    LOG_TRACE("trying to remove " << lit << " at depth " << depth << " along " << reason_clause);
    bool should_remove = true;
    for (Lit other : reason_clause) {
      if (other == ~lit) {
        continue;
      }
      if (minimize_literal(other, depth + 1)) {
        continue;
      }
      LOG_TRACE("could not remove literal " << other);
      should_remove = false;
      break;
    }
    if (depth > 0) {
      m_marks[var] = mark | (should_remove ? MarkRemovable : MarkPoisoned);
      m_marked.push_back(var);
    }
    LOG_TRACE("removing " << lit << " at depth " << depth << (should_remove ? " succeeded" : " failed"));
    return should_remove;
  }

  bool minimize_literal(Lit lit)
  {
    bool const minimize = minimize_literal(lit, 0);
    if (minimize) {
      LOG_TRACE("minimized literal " << lit);
    }
    return minimize;
  }

  void minimize_learned_clause()
  {
    assert(m_marked.empty());

    vector<Lit>& clause = tmp_analyze_clause; // the learned clause
    assert(clause.size() > 0);

    // Skip the first literal (the UIP on the highest decision level)
    auto const new_end = std::remove_if(clause.begin() + 1, clause.end(),
                                        [this](Lit lit) { return minimize_literal(lit); });

    ptrdiff_t const minimized = clause.end() - new_end;

    clause.erase(new_end, clause.end());
    LOG_DEBUG("minimized " << minimized << " literals");
    SUBSAT_STAT2_ADD(minimized_literals, minimized);

    // Clear 'poisoned' and 'removable' marks
    for (Var var : m_marked) {
      m_marks[var] &= MarkSeen;
    }
    m_marked.clear();
  }
#endif

  void unassign(Lit lit)
  {
    assert(m_unassigned_vars < m_used_vars);
    m_unassigned_vars += 1;

    assert(m_values[lit] == Value::True);
    assert(m_values[~lit] == Value::False);
    m_values[lit] = Value::Unassigned;
    m_values[~lit] = Value::Unassigned;

#if !SUBSAT_LEARN
    // If we aren't doing clause learning, we need to delete the redundant reasons
    Reason reason = m_vars[lit.var()].reason;
    if (reason.is_redundant()) {
      ConstraintRef cr = reason.get_clause_ref();
#ifndef NDEBUG
      assert(m_clause_refs.back() == cr);
      m_clause_refs.pop_back();
#endif
      m_constraints.unsafe_delete(cr);
      UPDATE_STORAGE_STATS();
    }
#endif

#if SUBSAT_VDOM
    m_vdom.unassigned(lit.var());
#endif
#if SUBSAT_VMTF
    m_queue.unassign(lit.var());
#endif
  }


  /// Backtrack to decision level 'new_level',
  /// i.e., undo all assignments on levels higher than 'new_level'.
  void backtrack(Level new_level)
  {
    LOG_INFO("Backtracking to level " << new_level);
    assert(new_level <= m_level);
#if SUBSAT_VMTF
    assert(m_queue.checkInvariants(m_values));
#endif

    while (!m_trail.empty()) {
      Lit const lit = m_trail.back();

      if (get_level(lit) == new_level) {
        break;
      }

      m_trail.pop_back();
      unassign(lit);
    }

    m_propagate_head = static_cast<uint32_t>(m_trail.size());
    m_theory_propagate_head = static_cast<uint32_t>(m_trail.size());
    m_level = new_level;
#if SUBSAT_VMTF
    assert(m_queue.checkInvariants(m_values));
#endif
  }  // backtrack


#if SUBSAT_RESTART
  void restart()
  {
    assert(checkInvariants());
    LOG_INFO("Restarting...");
    SUBSAT_STAT_INC(restarts);
    backtrack(0);
    assert(checkInvariants());
  }
#endif


#ifndef NDEBUG
  NODISCARD bool checkEmpty() const;
  NODISCARD bool checkConstraint(Constraint const& c) const;
  NODISCARD bool checkInvariants() const;
  NODISCARD bool checkWatches() const;
  NODISCARD bool checkModel() const;
#endif

#if SUBSAT_LOGGING_ENABLED
public:
  void showAssignment(std::ostream& os) const
  {
    bool first = true;
    Level prev_level = 0;
    for (Lit lit : m_trail) {
      if (first) {
        first = false;
      } else {
        os << " ";
      }
      Level const level = m_vars[lit.var()].level;
      if (level != prev_level) {
        os << "// ";
        prev_level = level;
      }
      os << lit;
    }
  }
private:
#endif

  Level get_level(Var var) const
  {
    assert(m_values[var] != Value::Unassigned);
    return m_vars[var].level;
  }

  Level get_level(Lit lit) const
  {
    return get_level(lit.var());
  }

  void get_binary_reason(Lit lit, Reason reason, Constraint& tmp_binary_clause) const
  {
    assert(reason.is_binary());
    assert(tmp_binary_clause.size() == 2);
    Lit other_lit = reason.get_binary_other_lit();
    tmp_binary_clause[0] = lit;
    tmp_binary_clause[1] = other_lit;
  }

  Constraint const& get_reason(Lit lit, Reason reason, Constraint& tmp_binary_clause) const
  {
    assert(reason.is_valid());
    if (reason.is_binary()) {
      get_binary_reason(lit, reason, tmp_binary_clause);
      return tmp_binary_clause;
    } else {
      return m_constraints.deref(reason.get_clause_ref());
    }
  }

private:
  /// Tracks the state the solver is in.
  State m_state = State::Unknown;

  /// Whether we found a conflict at the root level
  bool m_inconsistent = false;

  /// Number of active variables in the solver
  uint32_t m_used_vars = 0;

  /// Number of variables that have not yet been assigned
  uint32_t m_unassigned_vars = 0;

  /// Current decision level
  Level m_level = 0;

  /// Current assignment of literals.
  /// We store the value for both literal polarities to make the lookup simpler and branchless.
  vector_map<Lit, Value> m_values;

  /// Decision levels and reasons of variables
  vector_map<Var, VarInfo> m_vars;

  /// Mark flags of variables
  vector_map<Var, Mark> m_marks;

#if SUBSAT_VDOM
  /// Domain size decision heuristic
  vdom m_vdom;
#endif
#if SUBSAT_VMTF
  /// Queue for VMTF decision heuristic
  DecisionQueue m_queue;
#endif

#if SUBSAT_PHASE_SAVING
  // TODO
  // vector_map<Var, > m_phases;
#endif

  ConstraintArena m_constraints;
  // TODO: merge these
  vector_map<Lit, vector<Watch>> m_watches;
  vector_map<Lit, vector<Watch>> m_watches_amo;

#ifndef NDEBUG
  /// All proper clauses added to the solver
  vector<ConstraintRef> m_clause_refs;
  /// All AtMostOne constraints added to the solver
  vector<ConstraintRef> m_atmostone_constraint_refs;
#endif
  vector<std::pair<Constraint::Kind, ConstraintRef>> m_original_constraints;

  /// The currently true literals in order of assignment
  vector<Lit> m_trail;
  /// The next literal to propagate (index into the trail)
  uint32_t m_propagate_head = 0;
  /// The next literal to theory-propagate (index into the trail)
  uint32_t m_theory_propagate_head = 0;

  SubstitutionTheory m_theory;

  // Temporary variables, defined as class members to reduce allocation overhead.
  // Prefixed by the method where they are used.
  vector<Lit> tmp_analyze_clause;      ///< learned clause
  vector<Level> tmp_analyze_blocks;    ///< analyzed decision levels
  vector<Var> tmp_analyze_seen;        ///< analyzed variables
  vector<Var> m_marked;                ///< marked variables during conflict clause minimization
  vector_map<Level, uint8_t> m_frames; ///< stores for each level whether we already have it in blocks (we use 'char' because vector<bool> is bad)
  ConstraintRef tmp_propagate_binary_conflict_ref = ConstraintRef::invalid();

  Statistics m_stats;
  Limits m_limits;
}; // Solver

#if SUBSAT_LOGGING_ENABLED
inline std::ostream& operator<<(std::ostream& os, ShowAssignment sa)
{
  sa.solver.showAssignment(os);
  return os;
}
#endif


// TODO:
// 1. Tuning for expected-UNSAT:
//    - VMTF done
//    - fast restarts => very important
//    - clause deletion => if we have more than ~10k conflicts
//    - (sort analyzed variables before VMTF-bumping -- not so important according to Armin)
// 2. Instead of assumption (to switch between S/SR instance), allow resetting the solver while keeping the original clauses.
//    Maybe a separate ConstraintArena for learned clauses? (no, that just complicates the dereferencing of watch lists)
//    Store the ConstraintArena size when we added the last original clause and reset to that.
//    Then we want to be able to later add to finalized clauses: we need to extend the base_clauses by the negative matches.
//    Need to update the AMO's as well (and amo watch lists!); and add one AMO for the negative watches.
//    This doesn't seem too complicated (but hard making a "safe" interface to this, but we don't need to care about that right now).
// 3. binary clause optimization
// 4. phase saving? but for our problem, just choosing 'true' will almost always be correct.
//    => maybe add a 'hint' to 'new_variable'... that will be the first phase tried if we need to decide on it.
// 5. vsids / mode switching?
// 6. are we missing other important features?


#ifndef NDEBUG
#if SUBSAT_EXPENSIVE_ASSERTIONS

inline
bool Solver::checkEmpty() const
{
  assert(m_state == State::Unknown);
  assert(!m_inconsistent);
  assert(m_used_vars == 0);
  assert(m_unassigned_vars == 0);
  assert(m_level == 0);
  assert(m_values.empty());
  assert(m_vars.empty());
  assert(m_marks.empty());
#if SUBSAT_VDOM
  assert(m_vdom.empty());
#endif
#if SUBSAT_VMTF
  assert(m_queue.empty());
#endif
  assert(m_constraints.empty());
  assert(!tmp_propagate_binary_conflict_ref.is_valid());
#ifndef NDEBUG
  assert(m_clause_refs.empty());
  assert(m_atmostone_constraint_refs.empty());
#endif
  assert(m_original_constraints.empty());
  assert(std::all_of(m_watches.begin(), m_watches.end(),
                     [](vector<Watch> const& ws) { return ws.empty(); }));
  assert(std::all_of(m_watches_amo.begin(), m_watches_amo.end(),
                     [](vector<Watch> const& ws) { return ws.empty(); }));
  assert(m_trail.empty());
  assert(m_propagate_head == 0);
  assert(m_theory_propagate_head == 0);
  assert(tmp_analyze_clause.empty());
  assert(tmp_analyze_blocks.empty());
  assert(tmp_analyze_seen.empty());
  assert(m_frames.empty());
  assert(m_theory.empty());
  auto stats_ptr = reinterpret_cast<unsigned char const*>(&m_stats);
  assert(std::all_of(stats_ptr, stats_ptr + sizeof(Statistics),
                     [](unsigned char x) { return x == 0; }));
  return true;
}

inline
bool Solver::checkConstraint(Constraint const& c) const
{
  // No duplicate variables in the constraint (this prevents duplicate literals and tautological clauses)
  set<Var> vars;
  for (Lit lit : c) {
    assert(lit.is_valid());
    bool inserted = vars.insert(lit.var()).second;
    assert(inserted);
  }
  assert(vars.size() == c.size());
  return true;
}

inline
bool Solver::checkInvariants() const
{
  // assigned vars + unassiged vars = used vars
  assert(m_trail.size() + m_unassigned_vars == m_used_vars);

  assert(m_values.size() == 2 * m_used_vars);
  assert(std::all_of(m_values.begin(), m_values.end(),
                     [](Value v) { return v == Value::False || v == Value::True || v == Value::Unassigned; }));

  // m_unassigned_values is correct
  assert(std::count(m_values.begin(), m_values.end(), Value::Unassigned) == 2 * m_unassigned_vars);

  // Opposite literals have opposite values
  for (uint32_t var_idx = 0; var_idx < m_used_vars; ++var_idx) {
    Var x{var_idx};
    assert(m_values[x] == ~m_values[~x]);
  }

  // Every variable is at most once on the trail
  set<Var> trail_vars;
  for (Lit lit : m_trail) {
    assert(lit.is_valid());
    bool inserted = trail_vars.insert(lit.var()).second;
    assert(inserted);
  }
  assert(trail_vars.size() == m_trail.size());
  assert(m_trail.size() <= m_used_vars);

  // Decision level is the number of decisions on the trail
  auto num_decisions = std::count_if(m_trail.rbegin(), m_trail.rend(),
                                     [this](Lit lit) { return m_vars[lit.var()].is_decision(); });
  assert(m_level == num_decisions);

  assert(m_propagate_head <= m_trail.size());
  assert(m_theory_propagate_head <= m_trail.size());
  assert(m_propagate_head <= m_theory_propagate_head);

  // Check constraint invariants
  for (ConstraintRef cr : m_clause_refs) {
    assert(checkConstraint(m_constraints.deref(cr)));
  }
  for (ConstraintRef cr : m_atmostone_constraint_refs) {
    assert(checkConstraint(m_constraints.deref(cr)));
  }

  // Check watch invariants if we're in a fully propagated state
  if (m_propagate_head == m_trail.size()) {
    assert(checkWatches());
  }

  // Check reasons of assigned literals
  Constraint tmp_binary{2};  // a stack-allocated clause has space for two literals
  for (Lit const lit : m_trail) {
    Reason const reason = m_vars[lit.var()].reason;
    if (reason.is_valid()) {
      Constraint const& c = get_reason(lit, reason, tmp_binary);
      for (Lit const other : c) {
        assert(other == lit || m_values[other] == Value::False);
      }
    }
  }

  return true;
}  // checkInvariants

inline
bool Solver::checkWatches() const
{
  // Some of the checks only make sense in a fully-propagated state
  assert(m_propagate_head == m_trail.size());
  assert(!m_inconsistent);

  // All allocated but unused watch lists are empty
  for (uint32_t lit_idx = 2 * m_used_vars; lit_idx < m_watches.size(); ++lit_idx) {
    Lit const lit = Lit::from_index(lit_idx);
    assert(m_watches[lit].empty());
  }

  // Count how many times each clause is watched
  map<ConstraintRef::index_type, int> num_watches;

  for (uint32_t lit_idx = 0; lit_idx < m_watches.size(); ++lit_idx) {
    Lit const lit = Lit::from_index(lit_idx);

    for (Watch watch : m_watches[lit]) {
      Constraint const& clause = m_constraints.deref(watch.clause_ref);

      num_watches[watch.clause_ref.index()] += 1;

      // The watched literals are always the first two literals of the clause
      assert(clause[0] == lit || clause[1] == lit);

      // Check status of watch literals
      bool clause_satisfied = std::any_of(clause.begin(), clause.end(),
                                          [this](Lit l) { return m_values[l] == Value::True; });
      if (clause_satisfied) {
        Level min_true_level = std::numeric_limits<Level>::max();
        for (Lit l : clause) {
          if (m_values[l] == Value::True && get_level(l) < min_true_level) {
            min_true_level = get_level(l);
          }
        }
        // If the clause is satisfied and a watched literal is assigned,
        // it must be on the same level or above one of the true literals.
        assert(m_values[clause[0]] == Value::Unassigned || get_level(clause[0]) >= min_true_level);
        assert(m_values[clause[1]] == Value::Unassigned || get_level(clause[1]) >= min_true_level);
      } else {
        // If the clause is not yet satisfied, both watched literals must be unassigned
        // (otherwise we would have propagated them)
        assert(m_values[clause[0]] == Value::Unassigned && m_values[clause[1]] == Value::Unassigned);
      }
    }
  }
#if SUBSAT_LEARN  // if we're not learning, some of the clauses won't be watched
  // Every clause of size >= 2 is watched twice
  for (ConstraintRef cr : m_clause_refs) {
    Constraint const& c = m_constraints.deref(cr);
    if (c.size() >= 2) {
      auto it = num_watches.find(cr.index());
      assert(it != num_watches.end());
      assert(it->second == 2);
      num_watches.erase(it);
    }
  }
  assert(num_watches.empty());
#endif
  return true;
}

/// Checks whether the current assignment satisfies all constraints
inline
bool Solver::checkModel() const
{
  for (ConstraintRef cr : m_clause_refs) {
    Constraint const& c = m_constraints.deref(cr);
    bool satisfied = std::any_of(c.begin(), c.end(), [this](Lit l) { return m_values[l] == Value::True; });
    if (!satisfied) {
      LOG_WARN("Clause " << c << " is not satisfied!");
      return false;
    }
  }
  for (ConstraintRef cr : m_atmostone_constraint_refs) {
    Constraint const& c = m_constraints.deref(cr);
    uint32_t num_false = 0;
    uint32_t num_true = 0;
    uint32_t num_open = 0;
    for (Lit lit : c) {
      if (m_values[lit] == Value::True) { num_true += 1; }
      if (m_values[lit] == Value::Unassigned) { num_open += 1; }
      if (m_values[lit] == Value::False) { num_false += 1; }
    }
    assert(num_true + num_open + num_false == c.size());
    // AtMostOne constraint is satisfied if all or all but one literals are false
    bool satisfied = (num_false >= c.size() - 1);
    if (!satisfied) {
      LOG_WARN("AtMostOne constraint " << c << " is not satisfied!");
      return false;
    }
  }
  return true;
}

#else

inline
bool Solver::checkEmpty() const
{
  return true;
}

inline
bool Solver::checkConstraint(Constraint const& c) const
{
  return true;
}

inline
bool Solver::checkInvariants() const
{
  return true;
}

inline
bool Solver::checkWatches() const
{
  return true;
}

inline
bool Solver::checkModel() const
{
  return true;
}

#endif  // SUBSAT_EXPENSIVE_ASSERTIONS
#endif  // !defined(NDEBUG)



} // namespace subsat

#endif /* !SUBSAT_HPP */
