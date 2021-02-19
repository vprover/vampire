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
#include "./cdebug.hpp"

// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(VDEBUG == 0, "VDEBUG and NDEBUG are not synchronized");
#else
static_assert(VDEBUG == 1, "VDEBUG and NDEBUG are not synchronized");
#endif


// TODO: add feature flags for some optimizations where it's not 100% clear how much benefit they give us
//       the default values here can then be adjusted to what turns out to be best for the Vampire use case
#ifndef SUBSAT_PHASE_SAVING
#define SUBSAT_PHASE_SAVING 1
#endif



// TODO:
// Once this works, make a separate version 'matchsat',
// which keeps an array of matches as well.
// (see my notes on SAT+CSP)

namespace SMTSubsumption {


using Level = uint32_t;
#define InvalidLevel (std::numeric_limits<Level>::max())

struct VarInfo {
  Level level;
  ClauseRef reason;
};

struct Watch {
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


using Mark = unsigned char;
static constexpr Mark MarkSeen = 1;
static constexpr Mark MarkPoisoned = 2;  // since we probably won't do CC-minimization, we don't need "poisoned" and "removable"
static constexpr Mark MarkRemovable = 4;
// enum class Mark : char {
//   Seen = 1,
//   Poisoned = 2,
//   Removable = 4,
// };


class Solver
{
public:
  /// Ensure space for a new variable and return it.
  /// By default, memory is increased exponentially (relying on the default behaviour of std::vector).
  /// Use reserve_variables if you know the number of variables upfront.
  [[nodiscard]] Var new_variable()
  {
    // TODO: optional argument phase_hint as initial value for m_phases?
    Var new_var = Var{m_used_vars++};
    m_unassigned_vars++;
    m_vars.push_back({ .level = InvalidLevel, .reason = ClauseRef::invalid()});
    m_marks.push_back(0);
    m_values.push_back(Value::Unassigned); // value of positive literal
    m_values.push_back(Value::Unassigned); // value of negative literal
    while (m_watches.size() < 2 * m_used_vars) {
      m_watches.emplace_back().reserve(16);
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
    m_watches.reserve(2 * count);
    // TODO: call reserve on all vectors where this is necessary
  }


  /// Reset solver to empty state, but keep allocated memory buffers.
  void clear()
  {
    m_inconsistent = false;
    m_used_vars = 0;
    m_unassigned_vars = 0;
    m_level = 0;

    m_values.clear();
    m_vars.clear();
    m_marks.clear();

    m_queue.clear();

    m_clauses.clear();
    // Don't clear m_watches itself! We want to keep the nested vectors to save re-allocation.
    for (auto& watches : m_watches) {
      watches.clear();
    }

    m_trail.clear();
    m_propagate_head = 0;

    m_frames.clear();
  }

  /// Reserve space for a clause of 'capacity' literals
  /// and returns a handle to the storage.
  [[nodiscard]] AllocatedClauseHandle alloc_clause(uint32_t capacity)
  {
    return m_clauses.alloc(capacity);
  }

  void clause_start()
  {
    m_clauses.start();
  }

  void clause_literal(Lit lit)
  {
    m_clauses.push_literal(lit);
  }

  void clause_end()
  {
    ClauseRef cr = m_clauses.end();
    add_clause_internal(cr);
  }

  void add_clause(std::initializer_list<Lit> literals)
  {
    add_clause(literals.begin(), literals.size());
  }

  void add_clause(Lit const* literals, uint32_t count)
  {
    auto ca = m_clauses.alloc(count);
    for (Lit const* p = literals; p < literals + count; ++p) {
      ca.push(*p);
    }
    add_clause(ca);
  }

  void add_clause(AllocatedClauseHandle ca)
  {
    ClauseRef cr = ca.build();
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
        CDEBUG("skipping redundant unit clause: " << lit);
        break;
      case Value::False:
        CDEBUG("inconsistent unit clause: " << lit);
        m_inconsistent = true;
        break;
      case Value::Unassigned:
        CDEBUG("unit clause: " << lit);
        assign(lit, ClauseRef::invalid());
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
    Clause const& c = m_clauses.deref(cr);
    CDEBUG("add_clause: " << cr << " ~> " << c);
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
      watch_clause(cr);
    }
  }

  /// Preconditions:
  /// - all variables in the clause have been added using new_variable()
  /// - no duplicate variables in the clause
  /// - ???
  void add_clause_unsafe(Clause* clause)
  {
    // // TODO
    // ClauseRef cr = m_clauses.size();
    // CDEBUG("add_clause: " << cr << " ~> " << *clause);
    // m_clauses.push_back(clause);
    // watch_clause(cr);
  }

  Result solve();

private:

  /// Set the literal to true.
  /// Precondition: literal is not assigned.
  void assign(Lit lit, ClauseRef reason)
  {
    CDEBUG("assign: " << lit << ", reason: " << reason << ", level: " << m_level);

    /*
    // TODO: Assignment on root level => no need to store the reason
    // (done in satch, but not in kitten)
    // probably because this is only helpful when we have clause deletion?
    // if we don't delete clauses, we don't care if we store extra reason references.
    if (m_level == 0) {
      reason = ClauseRef::invalid();
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
    m_vars[var] = {
      .level = m_level,
      .reason = reason,
    };

    m_trail.push_back(lit);

    assert(m_unassigned_vars > 0);
    m_unassigned_vars -= 1;
  }

  /// Make a decision.
  void decide()
  {
    CDEBUG("decide");
    assert(m_unassigned_vars > 0);
    assert(!m_inconsistent);
    assert(m_level < m_used_vars);

    m_level += 1;

    assert(m_queue.checkInvariants(m_values));
    Var var = m_queue.next_unassigned_variable(m_values);

    // TODO: phase saving (+ hints?)
    // for now, just use the positive phase always (works quite well for our type of problems, or at least much better than always-negative)
    Lit decision{var, true};
    assign(decision, ClauseRef::invalid());
  }

  /// Unit propagation.
  /// Returns the conflicting clause when a conflict is encountered,
  /// or an invalid ClauseRef if all unit clauses have been propagated without conflict.
  ClauseRef propagate()
  {
    CDEBUG("propagate");
    // assert(checkInvariants());
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
  ClauseRef propagate_literal(Lit lit)
  {
    CDEBUG("propagate_literal: " << lit);
    // assert(checkInvariants());
    assert(m_values[lit] == Value::True);

    Lit const not_lit = ~lit;
    std::vector<Watch>& watches = m_watches[not_lit];

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
        // The replacement literal is true,
        // so it's enough to update the blocking literal.
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
        watch_literal(replacement, /* TODO: other_lit, */ clause_ref);
      }
      else if (other_value != Value::Unassigned) {
        // All literals in the clause are false => conflict
        assert(other_value == Value::False);
        conflict = clause_ref;
      }
      else {
        // All literals except other_lit are false => propagate
        assert(other_value == Value::Unassigned);
        assign(other_lit, clause_ref);
      }

    }  // while

    // Copy remaining watches
    while (p != watches.cend()) {
      *q++ = *p++;
    }
    watches.resize(std::distance(watches.begin(), q));
    assert(watches.end() == q);

    return conflict;
  }  // propagate_literal


  /// Watch literal 'lit' in the given clause.
  void watch_literal(Lit lit, /* TODO: Lit blocking_lit, */ ClauseRef clause_ref)
  {
    CDEBUG("watching " << lit << /* " blocked by " << blocking_lit << */ " in " << clause_ref);
    auto& watches = m_watches[lit];
    assert(std::all_of(watches.cbegin(), watches.cend(), [=](auto w){ return w.clause_ref != clause_ref; }));
    watches.push_back(Watch{clause_ref});
  }


  /// Watch the first two literals in the given clause.
  void watch_clause(ClauseRef clause_ref)
  {
    Clause const& clause = m_clauses.deref(clause_ref);
    assert(clause.size() >= 2);
    watch_literal(clause[0], /* TODO: clause[1], */ clause_ref);
    watch_literal(clause[1], /* TODO: clause[0], */ clause_ref);
  }


  /// Analyze conflict, learn a clause, backjump.
  /// Returns true if the search should continue.
  [[nodiscard]] bool analyze(ClauseRef conflict_ref)
  {
    CDEBUG("analyze: conflict clause " << conflict_ref);
    assert(!m_inconsistent);
    assert(checkInvariants());

    // assert(conflict_ref.is_valid());
    // Clause const& conflict = m_clauses.deref(conflict_ref);

    Level const conflict_level = m_level;
    if (conflict_level == 0) {
      // Conflict on root level
      m_inconsistent = true;
      return false;
    }

    std::vector<Lit>& clause = tmp_analyze_clause;
    std::vector<Level>& blocks = tmp_analyze_blocks;
    std::vector<Var>& seen = tmp_analyze_seen;
    vector_map<Level, char>& frames = m_frames;
    assert(clause.empty());
    assert(blocks.empty());
    assert(seen.empty());
    assert(frames.size() >= conflict_level);
    assert(std::all_of(frames.cbegin(), frames.cend(), [](auto x){ return x == 0; }));

    // Make room for the first UIP
    clause.push_back(Lit::invalid());

    auto t = m_trail.crbegin();
    uint32_t unresolved_on_conflict_level = 0;
    Lit uip = Lit::invalid();
    ClauseRef reason_ref = conflict_ref;

    while (true) {
      CDEBUG("reason_ref = " << reason_ref);
      assert(reason_ref.is_valid());
      Clause const& reason = m_clauses.deref(reason_ref);

      // TODO: reason->used = true

      CDEBUG("reason = " << reason);
      for (Lit const lit : reason) {
        Var const var = lit.var();
        CDEBUG("    checking lit " << lit << "  (uip = " << uip << ")");

        if (lit == uip)
          continue;  // TODO: why???

        Level const lit_level = get_level(var);
        CDEBUG("    lit_level = " << lit_level);
        if (lit_level == 0) {
          // no need to consider literals at level 0 since they are unconditionally true
          continue;
        }

        Mark const mark = m_marks[var];
        CDEBUG("    mark = " << (int)mark);
        assert(mark == 0 || mark == MarkSeen);
        if (mark) {
          continue;
        }
        m_marks[var] = MarkSeen;
        seen.push_back(var);

        assert(m_values[lit] == Value::False);
        if (lit_level < conflict_level) {
          if (!frames[lit_level]) {
            blocks.push_back(lit_level);
            frames[lit_level] = 1;
          }
          clause.push_back(lit);
        } else {
          assert(lit_level == conflict_level);
          unresolved_on_conflict_level++;
        }
      }  // for (lit : reason)

      // Find next literal to resolve by going backward over the trail
      do {
        assert(t < m_trail.crend());
        uip = *t;
        t++;
      } while (!m_marks[uip.var()]);

      unresolved_on_conflict_level--;
      if (unresolved_on_conflict_level == 0) {
        break;
      }

      reason_ref = m_vars[uip.var()].reason;
    }  // while(true)

    assert(uip.is_valid());
    Lit const not_uip = ~uip;
    clause[0] = not_uip;

    // CDEBUG("learning clause:");
    // for (Lit l : clause) {
    //   CDEBUG("    " << l);
    // }

    // TODO: cc-minimization?

    uint32_t const glue = blocks.size();
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

    uint32_t const size = clause.size();
    assert(size > 0);
    if (size == 1) {
      // We learned a unit clause
      assert(jump_level == 0);
      CDEBUG("learned unit: " << not_uip);
      assign(not_uip, ClauseRef::invalid());
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
        learned.push(learned_lit);
      }
      ClauseRef learned_ref = learned.build();
      // CDEBUG("learned: " << learned_ref << " ~> " << *learned);
      // TODO: call new_redundant_clause
      watch_clause(learned_ref);
      assign(not_uip, learned_ref);
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
    CDEBUG("backtrack to level " << new_level);
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

    m_propagate_head = m_trail.size();
    m_level = new_level;
    assert(m_queue.checkInvariants(m_values));
  }  // backtrack

#ifndef NDEBUG
  [[nodiscard]] bool checkInvariants() const;
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
  bool m_inconsistent = false;
  uint32_t m_used_vars = 0;
  uint32_t m_unassigned_vars = 0; ///< Number of variables that have not yet been assigned

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
  DecisionQueue m_queue;

#if SUBSAT_PHASE_SAVING
  // TODO
  // vector_map<Var, > m_phases;
#endif

  ClauseArena<> m_clauses;
  vector_map<Lit, std::vector<Watch>> m_watches;

  /// The currently true literals in order of assignment
  std::vector<Lit> m_trail;
  /// The next literal to propagate (index into the trail)
  uint32_t m_propagate_head = 0;

  // Temporary variables, defined as class members to reduce allocation overhead.
  // Prefixed by the method where they are used.
  std::vector<Lit> tmp_analyze_clause;  ///< learned clause
  std::vector<Level> tmp_analyze_blocks;  ///< analyzed decision levels
  std::vector<Var> tmp_analyze_seen;  ///< analyzed literals
  vector_map<Level, char> m_frames;  ///< stores for each level whether we already have it in blocks (we use 'char' because vector<bool> is bad)
}; // Solver


// TODO:
// 1. AtMostOne support
//    => needs special support for binary reasons so we don't have to materialize them
//    => can "chop off" highest bit of ClauseRef to embed literals in there?
//       (using highest bit means no arithmetic is required for normal clause indexing)
//       this would also allow us to easily do the binary clause optimization in watch lists.
//       although for that, it might be better to use blocking literals + invalid clauseref for binary watches
// 2. binary clause optimization
// 3. phase saving? but for our problem, just choosing 'true' will almost always be correct.
//    => maybe add a 'hint' to 'new_variable'... that will be the first phase tried if we need to decide on it.


} // namespace SMTSubsumption

#endif /* !SUBSAT_HPP */
