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
#include <set>
#include <map>
#include <vector>

#include "./clause.hpp"
#include "./decision_queue.hpp"
#include "./types.hpp"
#include "./vector_map.hpp"
#include "./log.hpp"
#include "../SubstitutionTheory2.hpp"

// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(VDEBUG == 0, "VDEBUG and NDEBUG are not synchronized");
#else
static_assert(VDEBUG == 1, "VDEBUG and NDEBUG are not synchronized");
#endif


// TODO: add feature flags for some optimizations where it's not 100% clear how much benefit they give us
//       the default values here can then be adjusted to what turns out to be best for the Vampire use case
#ifndef SUBSAT_PHASE_SAVING
#define SUBSAT_PHASE_SAVING 0
#endif



// TODO:
// Once this works, make a separate version 'matchsat',
// which keeps an array of matches as well.
// (see my notes on SAT+CSP)

namespace subsat {


using Level = uint32_t;
#define InvalidLevel (std::numeric_limits<Level>::max())

class Reason final {
  enum class Type : uint8_t {
    Invalid,
    Binary,
    ClauseRef,
  };

  Type type = Type::Invalid;

  union {
    Lit binary_other_lit;
    ClauseRef clause_ref;
  };

public:
  constexpr Reason() noexcept
    : type{Type::Invalid}
    , clause_ref{ClauseRef::invalid()}
  { }

  explicit Reason(Lit other) noexcept
    : type{Type::Binary}
    , binary_other_lit{other}
  {
    assert(other.is_valid());
  }

  explicit Reason(ClauseRef cr) noexcept
    : type{Type::ClauseRef}
    , clause_ref{cr}
  {
    assert(cr.is_valid());
  }

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

  ClauseRef get_clause_ref() const noexcept
  {
    assert(type == Type::ClauseRef);
    return clause_ref;
  }
};
static_assert(std::is_trivially_destructible<Reason>::value, "");

struct VarInfo final {
  Level level = InvalidLevel;
  Reason reason;
};
static_assert(std::is_trivially_destructible<VarInfo>::value, "");

struct Watch final {
  constexpr Watch() noexcept
    : clause_ref{ClauseRef::invalid()}
  { }

  constexpr Watch(ClauseRef cr) noexcept
    : clause_ref{cr}
  { }

  // TODO: optimizations: binary clause, blocking literal
  //       (although kitten doesn't seem to do either of those)
  ClauseRef clause_ref;
};
static_assert(std::is_trivially_destructible<Watch>::value, "");


using Mark = unsigned char;
static constexpr Mark MarkSeen = 1;
static constexpr Mark MarkPoisoned = 2;  // since we probably won't do CC-minimization, we don't need "poisoned" and "removable"
static constexpr Mark MarkRemovable = 4;
// enum class Mark : char {
//   Seen = 1,
//   Poisoned = 2,
//   Removable = 4,
// };

#if LOGGING_ENABLED
template <template <typename> class A>
struct ShowClauseRef {
  ShowClauseRef(ClauseArena<A> const& arena, ClauseRef cr) noexcept
    : arena(arena), cr(cr)
  { }
  ClauseArena<A> const& arena;
  ClauseRef cr;
};

template <template <typename> class A>
std::ostream& operator<<(std::ostream& os, ShowClauseRef<A> const& scr)
{
  if (scr.cr.is_valid()) {
    os << scr.arena.deref(scr.cr);
  } else {
    os << "{-}";
  }
  return os;
}

template <template <typename> class A>
struct ShowReason {
  ShowReason(ClauseArena<A> const& arena, Reason r) noexcept
    : arena(arena), r(r)
  { }
  ClauseArena<A> const& arena;
  Reason r;
};

template <template <typename> class A>
std::ostream& operator<<(std::ostream& os, ShowReason<A> const& sr)
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

template <template <typename> class Allocator> class Solver;

template <template <typename> class A>
struct ShowAssignment {
  ShowAssignment(Solver<A> const& solver) : solver(solver) { }
  Solver<A> const& solver;
};

template <template <typename> class A>
std::ostream& operator<<(std::ostream& os, ShowAssignment<A> sa);
#endif

template <template <typename> class Allocator = std::allocator>
class Solver {
#define SHOWREF(cr) (ShowClauseRef<Allocator>{m_clauses, cr})
#define SHOWREASON(r) (ShowReason<Allocator>{m_clauses, r})
#define SHOWASSIGNMENT() (ShowAssignment<Allocator>{*this})

public:
  template <typename T>
  using allocator_type = Allocator<T>;

  template <typename T>
  using vector = std::vector<T, allocator_type<T>>;

  template <typename K, typename T>
  using vector_map = subsat::vector_map<K, T, allocator_type<T>>;


  /// Ensure space for a new variable and return it.
  /// By default, memory is increased exponentially (relying on the default behaviour of std::vector).
  /// Use reserve_variables if you know the number of variables upfront.
  NODISCARD Var new_variable()
  {
    // TODO: optional argument phase_hint as initial value for m_phases?
    Var new_var = Var{m_used_vars++};
    m_unassigned_vars++;
    m_vars.emplace_back();
    m_marks.push_back(0);
    m_values.push_back(Value::Unassigned);  // value of positive literal
    m_values.push_back(Value::Unassigned);  // value of negative literal
    while (m_watches.size() < 2 * m_used_vars) {
      m_watches.emplace_back();             // positive literal watches
      m_watches.emplace_back();             // negative literal watches
    }
    while (m_watches_amo.size() < 2 * m_used_vars) {
      m_watches_amo.emplace_back();         // positive literal watches
      m_watches_amo.emplace_back();         // positive literal watches -- generally not needed for our instances
    }
    return new_var;
  }

  /// Reserve space for 'count' variables (in total),
  /// but does not actually enable the new variables in the solver.
  void reserve_variables(uint32_t count)
  {
    m_vars.reserve(count);
    m_marks.reserve(count);
    m_values.reserve(2 * count);
    m_queue.reserve(count);
    m_watches.reserve(2 * count);
    m_watches_amo.reserve(2 * count);
    m_trail.reserve(count);

    tmp_analyze_clause.reserve(8);
    tmp_analyze_blocks.reserve(8);
    tmp_analyze_seen.reserve(16);
    m_frames.reserve(count+1);
  }

  /// Reserve storage for 'count' literals (less will be available since clause header is stored in the same space)
  void reserve_clause_storage(uint32_t count)
  {
    m_clauses.reserve(count);
  }

  ::SMTSubsumption::SubstitutionTheory2<allocator_type>& theory()
  {
    return m_theory;
  }


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

    m_inconsistent = false;
    m_used_vars = 0;
    m_unassigned_vars = 0;
    m_level = 0;

    m_values.clear();
    m_vars.clear();
    m_marks.clear();

    m_queue.clear();

    m_clauses.clear();
    tmp_binary_clause_ref = ClauseRef::invalid();
#ifndef NDEBUG
    m_clause_refs.clear();
    m_atmostone_constraint_refs.clear();
#endif

    // Don't clear m_watches itself! We want to keep the nested vectors to save re-allocation.
    uint32_t const used_watches = 2 * old_used_vars;
    for (uint32_t i = 0; i < used_watches; ++i) {
      m_watches[Lit::from_index(i)].clear();
      m_watches_amo[Lit::from_index(i)].clear();
    }
    // for (auto& w : m_watches) { w.clear(); }
    // for (auto& w : m_watches_amo) { w.clear(); }

    m_trail.clear();
    m_propagate_head = 0;
    m_theory_propagate_head = 0;

    m_frames.clear();

    m_theory.clear();

    assert(checkEmpty());
  }

  /// Reserve space for a clause of 'capacity' literals
  /// and returns a handle to the storage.
  NODISCARD AllocatedClauseHandle alloc_clause(uint32_t capacity)
  {
    return m_clauses.alloc(capacity);
  }

  void handle_push_literal(AllocatedClauseHandle& handle, Lit lit) noexcept
  {
    m_clauses.handle_push_literal(handle, lit);
  }

  void clause_start()
  {
    m_clauses.start();
  }

  void clause_literal(Lit lit)
  {
    m_clauses.push_literal(lit);
  }

  NODISCARD ClauseRef clause_end()
  {
    return m_clauses.end();
  }

  void add_clause(ClauseRef cr)
  {
    add_clause_internal(cr);
  }

  void add_clause(std::initializer_list<Lit> literals)
  {
    assert(literals.size() <= UINT32_MAX);
    auto literals_size = static_cast<uint32_t>(literals.size());
    add_clause(literals.begin(), literals_size);
  }

  void add_clause(Lit const* literals, uint32_t count)
  {
    auto ca = m_clauses.alloc(count);
    for (Lit const* p = literals; p < literals + count; ++p) {
      handle_push_literal(ca, *p);
    }
    add_clause(ca);
  }

  void add_clause(AllocatedClauseHandle& handle)
  {
    ClauseRef cr = m_clauses.handle_build(handle);
    add_clause_internal(cr);
  }

  void add_empty_clause()
  {
    m_inconsistent = true;
  }

  void ensure_variable(Var var)
  {
    while (var.index() >= m_used_vars) {
      (void)new_variable();
    }
  }

  void add_unit_clause(Lit lit)
  {
    ensure_variable(lit.var());
    switch (m_values[lit]) {
      case Value::True:
        LOG_INFO("skipping redundant unit clause: " << lit);
        break;
      case Value::False:
        LOG_INFO("inconsistent unit clause: " << lit);
        m_inconsistent = true;
        break;
      case Value::Unassigned:
        LOG_INFO("adding unit clause: " << lit);
        assign(lit, Reason::invalid());
        break;
    }
  }

  void add_binary_clause(Lit lit1, Lit lit2)
  {
    // TODO: special handling for binary clauses
    add_clause({lit1, lit2});
  }

  void add_clause_internal(ClauseRef cr)
  {
    LOG_INFO("Adding clause " << SHOWREF(cr));

    Clause const& c = m_clauses.deref(cr);
    // TODO: improve this?
    for (Lit lit : c) {
      ensure_variable(lit.var());
    }
    // TODO: check for duplicate variables
    if (c.size() == 0) {
      add_empty_clause();
    } else if (c.size() == 1) {
      add_unit_clause(c[0]);
    } else {
      // TODO: special handling for binary clauses
      assert(c.size() >= 2);
#ifndef NDEBUG
      m_clause_refs.push_back(cr);
#endif
      watch_clause(cr);
    }
  }

  /// Preconditions:
  /// - all variables in the clause have been added using new_variable()
  /// - no duplicate variables in the clause
  /// - ???
  void add_clause_unsafe(Clause* clause)
  {
    // TODO
    (void)clause;
  }

  void add_atmostone_constraint(std::initializer_list<Lit> literals)
  {
    assert(literals.size() <= UINT32_MAX);
    auto literals_size = static_cast<uint32_t>(literals.size());
    add_atmostone_constraint(literals.begin(), literals_size);
  }

  void add_atmostone_constraint(Lit const* literals, uint32_t count)
  {
    auto ca = m_clauses.alloc(count);
    for (Lit const* p = literals; p < literals + count; ++p) {
      handle_push_literal(ca, *p);
    }
    add_atmostone_constraint(ca);
  }

  void add_atmostone_constraint(AllocatedClauseHandle handle)
  {
    ClauseRef cr = m_clauses.handle_build(handle);
    add_atmostone_constraint_internal(cr);
  }

  void add_atmostone_constraint_internal(ClauseRef cr)
  {
    LOG_INFO("adding AtMostOne constraint " << SHOWREF(cr));

    Clause const& c = m_clauses.deref(cr);
    // TODO: improve this?
    for (Lit lit : c) {
      ensure_variable(lit.var());
    }
    // TODO: check for assigned and duplicate variables
    if (c.size() <= 1) {
      // AtMostOne constraints of sizes 0 and 1 are tautologies => do nothing
    } else if (c.size() == 2) {
      // AtMostOne constraint of size 2 is a binary clause
      add_clause_internal(cr);
    } else {
      // Add proper AtMostOne constraint
      assert(c.size() >= 3);
#ifndef NDEBUG
      m_atmostone_constraint_refs.push_back(cr);
#endif
      watch_atmostone_constraint(cr);
    }
  }
  /// Returns true iff the solver is in an inconsistent state.
  /// (may return true before calling solve() if e.g. an empty clause is added.)
  bool inconsistent() const
  {
    return m_inconsistent;
  }

  Result solve()
  {
    m_trail.reserve(m_used_vars);
    m_frames.resize(m_used_vars + 1, 0);
    m_queue.resize_and_init(m_used_vars);
    assert(m_queue.checkInvariants(m_values));

    if (!tmp_binary_clause_ref.is_valid()) {
      auto ca = m_clauses.alloc(2);
      handle_push_literal(ca, Lit::invalid());
      handle_push_literal(ca, Lit::invalid());
      tmp_binary_clause_ref = m_clauses.handle_build(ca);
    }

    if (m_inconsistent) {
      return Result::Unsat;
    }

    while (true) {
      ClauseRef conflict = propagate();

      assert(checkInvariants());

      if (conflict.is_valid()) {
        if (!analyze(conflict)) {
          return Result::Unsat;
        }
      } else {
        if (m_unassigned_vars == 0) {
          assert(checkModel());
          return Result::Sat;
        } else {
          // TODO: restart? switch mode? reduce clause db?
          decide();
        }
      }
    }
  }

private:

  /// Set the literal to true.
  /// Precondition: literal is not assigned.
  void basic_assign(Lit lit, Reason reason)
  {
    LOG_DEBUG("Assigning " << lit << ", reason: " << SHOWREASON(reason) << ", level: " << m_level);

    /*
    // TODO: Assignment on root level => no need to store the reason
    // (done in satch, but not in kitten)
    // probably because this is only helpful when we have clause deletion?
    // if we don't delete clauses, we don't care if we store extra reason references.
    if (m_level == 0) {
      reason = Reason::invalid();
    } */

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

    assert(m_unassigned_vars > 0);
    m_unassigned_vars -= 1;
  }

  void assign(Lit lit, Reason reason)
  {
    basic_assign(lit, reason);
    if (!m_theory.empty()) {
      theory_propagate();
    } else {
      m_theory_propagate_head = static_cast<uint32_t>(m_trail.size());
    }
  }

  void theory_propagate()
  {
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
                basic_assign(propagated, Reason{reason});
              } else {
                assert(m_values[propagated] == Value::True);
              }
              return true;
            });
        assert(enabled);
      }
    }
  }

  /// Make a decision.
  void decide()
  {
    assert(m_unassigned_vars > 0);
    assert(!m_inconsistent);
    assert(m_level < m_used_vars);

    m_level += 1;

    assert(m_queue.checkInvariants(m_values));
    Var var = m_queue.next_unassigned_variable(m_values);

    // TODO: phase saving (+ hints?)
    // for now, just use the positive phase always (works quite well for our type of problems, or at least much better than always-negative)
    Lit decision{var, true};
    LOG_DEBUG("decision: " << decision);
    assign(decision, Reason::invalid());
  }

  /// Unit propagation.
  /// Returns the conflicting clause when a conflict is encountered,
  /// or an invalid ClauseRef if all unit clauses have been propagated without conflict.
  ClauseRef propagate()
  {
    // CDEBUG("propagate");
    // assert(checkInvariants());
    assert(m_theory_propagate_head == m_trail.size());
    while (m_propagate_head < m_trail.size()) {
      Lit const lit = m_trail[m_propagate_head++];
      ClauseRef const conflict = propagate_literal(lit);
      if (conflict.is_valid()) {
        return conflict;
      }
    }
    return ClauseRef::invalid();
  }

  /// Unit propagation for the given literal.
  ClauseRef propagate_literal(Lit const lit)
  {
    LOG_DEBUG("Propagating " << lit);
    // assert(checkInvariants());
    assert(m_values[lit] == Value::True);

    Lit const not_lit = ~lit;

    // Propagate AtMostOne constraints.
    // There's no need to copy/modify any watches here,
    // because as soon as an AtMostOne constraint triggers,
    // all other literals will be set to false immediately.
    for (Watch const& watch : m_watches_amo[lit]) {
      ClauseRef const cr = watch.clause_ref;
      Clause& c = m_clauses.deref(cr);
      assert(c.size() >= 3);
      for (Lit other_lit : c) {
        if (lit == other_lit) {
          continue;
        }
        Value const other_value = m_values[other_lit];
        if (other_value == Value::Unassigned) {
          // propagate
          LOG_TRACE("Assigning " << ~other_lit << " due to AtMostOne constraint " << SHOWREF(cr));
          assign(~other_lit, Reason{lit});
        }
        else if (other_value == Value::True) {
          LOG_TRACE("Current assignment: " << SHOWASSIGNMENT());
          LOG_DEBUG("Conflict with AtMostOne constraint " << SHOWREF(cr));
          // at least two literals in the AtMostOne constraint are true => conflict
          Clause& tmp_binary_clause = m_clauses.deref(tmp_binary_clause_ref);
          tmp_binary_clause[0] = not_lit;
          tmp_binary_clause[1] = ~other_lit;
          return tmp_binary_clause_ref;
        }
        else {
          assert(other_value == Value::False);
          // nothing to do
        }
      }
    }

    vector<Watch>& watches = m_watches[not_lit];

    auto q = watches.begin();   // points to updated watch, follows p
    auto p = watches.cbegin();  // points to currently processed watch

    ClauseRef conflict = ClauseRef::invalid();

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

      ClauseRef const clause_ref = watch.clause_ref;
      Clause& clause = m_clauses.deref(clause_ref);
      assert(clause.size() >= 2);

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
      }
      else if (other_value != Value::Unassigned) {
        // All literals in the clause are false => conflict
        assert(other_value == Value::False);
        conflict = clause_ref;
      }
      else {
        // All literals except other_lit are false => propagate
        assert(other_value == Value::Unassigned);
        LOG_TRACE("Assigning " << other_lit << " due to clause " << SHOWREF(clause_ref));
        assign(other_lit, Reason{clause_ref});
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
  }  // propagate_literal


  /// Watch literal 'lit' in the given clause.
  void watch_clause_literal(Lit lit, /* TODO: Lit blocking_lit, */ ClauseRef clause_ref)
  {
    LOG_DEBUG("Watching " << lit << /* " blocked by " << blocking_lit << */ " in " << SHOWREF(clause_ref));
    auto& watches = m_watches[lit];
    assert(std::all_of(watches.cbegin(), watches.cend(), [=](Watch w){ return w.clause_ref != clause_ref; }));
    watches.push_back(Watch{clause_ref});
  }


  /// Watch the first two literals in the given clause.
  void watch_clause(ClauseRef clause_ref)
  {
    Clause const& clause = m_clauses.deref(clause_ref);
    assert(clause.size() >= 2);
    watch_clause_literal(clause[0], /* TODO: clause[1], */ clause_ref);
    watch_clause_literal(clause[1], /* TODO: clause[0], */ clause_ref);
  }


  /// Watch every literal in the AtMostOne constraint
  void watch_atmostone_constraint(ClauseRef cr)
  {
    Clause const& c = m_clauses.deref(cr);
    assert(c.size() >= 3);
    for (Lit lit : c) {
      auto& watches = m_watches_amo[lit];
      assert(std::all_of(watches.cbegin(), watches.cend(), [=](Watch w) { return w.clause_ref != cr; }));
      watches.push_back(Watch{cr});
    }
  }


  /// Analyze conflict, learn a clause, backjump.
  /// Returns true if the search should continue.
  NODISCARD bool analyze(ClauseRef conflict_ref)
  {
    LOG_INFO("Conflict clause " << SHOWREF(conflict_ref) << " on level " << m_level);
    LOG_TRACE("Assignment: " << SHOWASSIGNMENT());
    assert(!m_inconsistent);
    assert(conflict_ref.is_valid());
    assert(checkInvariants());

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
    ClauseRef reason_ref = conflict_ref;

    while (true) {
      LOG_TRACE("Reason: " << SHOWREF(reason_ref) << ", uip: " << uip << ", unresolved: " << unresolved_on_conflict_level);
      assert(reason_ref.is_valid());
      Clause const& reason_clause = m_clauses.deref(reason_ref);

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

        LOG_TRACE("    blocks: " << SHOWVEC(blocks));
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

      Reason const& reason = m_vars[uip.var()].reason;
      if (reason.is_binary()) {
        // recover binary reason clause
        Lit other_lit = reason.get_binary_other_lit();
        Clause& tmp_binary_clause = m_clauses.deref(tmp_binary_clause_ref);
        tmp_binary_clause[0] = uip;  // will be skipped
        tmp_binary_clause[1] = ~other_lit;
        reason_ref = tmp_binary_clause_ref;
      } else {
        reason_ref = reason.get_clause_ref();
      }
    }  // while(true)

    // TODO: analyze loop is a bit simpler in kitten, maybe we can do that too?
    //       kitten does not use any blocks/frames (we don't really use them here either)

    assert(uip.is_valid());
    Lit const not_uip = ~uip;
    clause[0] = not_uip;
    LOG_TRACE("Learning clause: " << SHOWVEC(clause));

    // TODO: cc-minimization?

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
      m_queue.move_to_front(var);
      assert(m_marks[var]);
      m_marks[var] = 0;
    }
    seen.clear();
    assert(m_queue.checkInvariants(m_values));

    backtrack(jump_level);

    uint32_t const size = static_cast<uint32_t>(clause.size());
    assert(size > 0);
    if (size == 1) {
      // We learned a unit clause
      assert(jump_level == 0);
      LOG_INFO("Learned unit: " << not_uip);
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

      auto learned = m_clauses.alloc(size);
      for (Lit learned_lit : clause) {
        handle_push_literal(learned, learned_lit);
      }
      ClauseRef learned_ref = m_clauses.handle_build(learned);
      LOG_INFO("Learned: " << SHOWREF(learned_ref));
      // TODO: call new_redundant_clause
      add_clause_internal(learned_ref);
      assign(not_uip, Reason{learned_ref});
    }

    clause.clear();

    return true;
  }  // analyze



  void unassign(Lit lit)
  {
    assert(m_unassigned_vars < m_used_vars);
    m_unassigned_vars += 1;

    assert(m_values[lit] == Value::True);
    assert(m_values[~lit] == Value::False);
    m_values[lit] = Value::Unassigned;
    m_values[~lit] = Value::Unassigned;

    m_queue.unassign(lit.var());
  }


  void backtrack(Level new_level)
  {
    LOG_INFO("Backtracking to level " << new_level);
    assert(new_level <= m_level);
    assert(m_queue.checkInvariants(m_values));

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
    assert(m_queue.checkInvariants(m_values));
  }  // backtrack

#ifndef NDEBUG
  NODISCARD bool checkEmpty() const;
  NODISCARD bool checkInvariants() const;
  NODISCARD bool checkWatches() const;
  NODISCARD bool checkModel() const;
#endif

#if LOGGING_ENABLED
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
  // friend std::ostream& operator<<(std::ostream&, ShowAssignment<allocator_type>);
private:
#endif

  Level get_level(Var var) const
  {
    return m_vars[var].level;
  }

  Level get_level(Lit lit) const
  {
    return get_level(lit.var());
  }

private:
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

  /// Queue for VMTF decision heuristic
  DecisionQueue<allocator_type> m_queue;

#if SUBSAT_PHASE_SAVING
  // TODO
  // vector_map<Var, > m_phases;
#endif

  ClauseArena<Allocator> m_clauses;
  vector_map<Lit, vector<Watch>> m_watches;
  vector_map<Lit, vector<Watch>> m_watches_amo;

#ifndef NDEBUG
  /// All proper clauses added to the solver
  vector<ClauseRef> m_clause_refs;
  /// All AtMostOne constraints added to the solver
  vector<ClauseRef> m_atmostone_constraint_refs;
#endif

  /// The currently true literals in order of assignment
  vector<Lit> m_trail;
  /// The next literal to propagate (index into the trail)
  uint32_t m_propagate_head = 0;
  /// The next literal to theory-propagate (index into the trail)
  uint32_t m_theory_propagate_head = 0;

  ::SMTSubsumption::SubstitutionTheory2<allocator_type> m_theory;

  // Temporary variables, defined as class members to reduce allocation overhead.
  // Prefixed by the method where they are used.
  vector<Lit> tmp_analyze_clause;  ///< learned clause
  vector<Level> tmp_analyze_blocks;  ///< analyzed decision levels
  vector<Var> tmp_analyze_seen;  ///< analyzed variables
  vector_map<Level, uint8_t> m_frames;  ///< stores for each level whether we already have it in blocks (we use 'char' because vector<bool> is bad)
  ClauseRef tmp_binary_clause_ref = ClauseRef::invalid();
}; // Solver

#if LOGGING_ENABLED
template <template <typename> class A>
std::ostream& operator<<(std::ostream& os, ShowAssignment<A> sa)
{
  sa.solver.showAssignment(os);
  return os;
}
#endif


// TODO:
// 1. sort analyzed variables before VMTF-bumping
// 2. binary clause optimization
// 3. phase saving? but for our problem, just choosing 'true' will almost always be correct.
//    => maybe add a 'hint' to 'new_variable'... that will be the first phase tried if we need to decide on it.
// 4. restarts
// 5. vsids / mode switching?
// 6. are we missing other important minisat features? (clause deletion, CC-minimization, ...?)


#ifndef NDEBUG

template <template <typename> class Allocator>
bool Solver<Allocator>::checkEmpty() const
{
  assert(!m_inconsistent);
  assert(m_used_vars == 0);
  assert(m_unassigned_vars == 0);
  assert(m_level == 0);
  assert(m_values.empty());
  assert(m_vars.empty());
  assert(m_marks.empty());
  assert(m_queue.empty());
  assert(m_clauses.empty());
  assert(!tmp_binary_clause_ref.is_valid());
#ifndef NDEBUG
  assert(m_clause_refs.empty());
  assert(m_atmostone_constraint_refs.empty());
#endif
  assert(std::all_of(m_watches.begin(), m_watches.end(), [](vector<Watch> const& ws){ return ws.empty(); }));
  assert(std::all_of(m_watches_amo.begin(), m_watches_amo.end(), [](vector<Watch> const& ws){ return ws.empty(); }));
  assert(m_trail.empty());
  assert(m_propagate_head == 0);
  assert(m_theory_propagate_head == 0);
  assert(tmp_analyze_clause.empty());
  assert(tmp_analyze_blocks.empty());
  assert(tmp_analyze_seen.empty());
  assert(m_frames.empty());
  assert(m_theory.empty());
  return true;
}

static NODISCARD bool checkConstraint(Clause const& c)
{
  // No duplicate variables in the constraint (this prevents duplicate literals and tautological clauses)
  std::set<Var> vars;
  for (Lit lit : c) {
    assert(lit.is_valid());
    bool inserted = vars.insert(lit.var()).second;
    assert(inserted);
  }
  assert(vars.size() == c.size());
  return true;
}

template <template <typename> class Allocator>
bool Solver<Allocator>::checkInvariants() const
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
  std::set<Var> trail_vars;
  for (Lit lit : m_trail) {
    assert(lit.is_valid());
    bool inserted = trail_vars.insert(lit.var()).second;
    assert(inserted);
  }
  assert(trail_vars.size() == m_trail.size());
  assert(m_trail.size() <= m_used_vars);

  assert(m_propagate_head <= m_trail.size());
  assert(m_theory_propagate_head <= m_trail.size());
  assert(m_propagate_head <= m_theory_propagate_head);

  // Check constraint invariants
  for (ClauseRef cr : m_clause_refs) {
    assert(checkConstraint(m_clauses.deref(cr)));
  }
  for (ClauseRef cr : m_atmostone_constraint_refs) {
    assert(checkConstraint(m_clauses.deref(cr)));
  }

  // Check watch invariants if we're in a fully propagated state
  if (m_propagate_head == m_trail.size()) {
    assert(checkWatches());
  }

  return true;
}  // checkInvariants

template <template <typename> class Allocator>
bool Solver<Allocator>::checkWatches() const
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
  std::map<ClauseRef::index_type, int> num_watches;

  for (uint32_t lit_idx = 0; lit_idx < m_watches.size(); ++lit_idx) {
    Lit const lit = Lit::from_index(lit_idx);

    for (Watch watch : m_watches[lit]) {
      Clause const& clause = m_clauses.deref(watch.clause_ref);

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
  // Every clause of size >= 2 is watched twice
  for (ClauseRef cr : m_clause_refs) {
    Clause const& c = m_clauses.deref(cr);
    if (c.size() >= 2) {
      auto it = num_watches.find(cr.index());
      assert(it != num_watches.end());
      assert(it->second == 2);
      num_watches.erase(it);
    }
  }
  assert(num_watches.empty());
  return true;
}

/// Checks whether the current assignment satisfies all constraints
template <template <typename> class Allocator>
bool Solver<Allocator>::checkModel() const
{
  for (ClauseRef cr : m_clause_refs) {
    Clause const& c = m_clauses.deref(cr);
    bool satisfied = std::any_of(c.begin(), c.end(), [this](Lit l) { return m_values[l] == Value::True; });
    if (!satisfied) {
      LOG_WARN("Clause " << c << " is not satisfied!");
      return false;
    }
  }
  for (ClauseRef cr : m_atmostone_constraint_refs) {
    Clause const& c = m_clauses.deref(cr);
    uint32_t num_false = 0;
    uint32_t num_true = 0;
    uint32_t num_open = 0;
    for (Lit lit : c) {
      if (m_values[lit] == Value::True) { num_true += 1; }
      if (m_values[lit] == Value::Unassigned) { num_open += 1; }
      if (m_values[lit] == Value::False) { num_false += 1; }
    }
    assert(num_true + num_open + num_false == c.size());
    // AtMostOne constraint is satisfied if all but one literals are false
    bool satisfied = (num_false == c.size() - 1);
    if (!satisfied) {
      LOG_WARN("AtMostOne constraint " << c << " is not satisfied!");
      return false;
    }
  }
  return true;
}

#endif



} // namespace subsat

#endif /* !SUBSAT_HPP */
