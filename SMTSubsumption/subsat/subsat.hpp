#ifndef SUBSAT_HPP
#define SUBSAT_HPP

#include <algorithm>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iterator>
#include <limits>
#include <new>
#include <ostream>
#include <set>
#include <map>
#include <vector>

#include "./alloc.hpp"
#include "./types.hpp"
#include "ivector.hpp"
#include "cdebug.hpp"

// Ensure NDEBUG and VDEBUG are synchronized
#ifdef NDEBUG
static_assert(!VDEBUG, "");
#else
static_assert(VDEBUG, "");
#endif

// TODO:
// Once this works, make a separate version 'matchsat',
// which keeps an array of matches as well.
// (see my notes on SAT+CSP)

namespace SMTSubsumption {


class Clause final {
public:
  using iterator = Lit*;
  using const_iterator = Lit const*;
  using size_type = uint32_t;

  iterator begin() noexcept
  {
    return &m_literals[0];
  }

  iterator end() noexcept
  {
    return begin() + m_size;
  }

  const_iterator begin() const noexcept
  {
    return cbegin();
  }

  const_iterator end() const noexcept
  {
    return cend();
  }

  const_iterator cbegin() const noexcept
  {
    return &m_literals[0];
  }

  const_iterator cend() const noexcept
  {
    return cbegin() + m_size;
  }

  Lit& operator[](size_type idx) noexcept
  {
    assert(idx < m_size);
    return m_literals[idx];
  }

  Lit const& operator[](size_type idx) const noexcept
  {
    assert(idx < m_size);
    return m_literals[idx];
  }

  size_type size() const noexcept
  {
    return m_size;
  }

  /// Number of bytes required by a clause containing 'size' literals.
  static size_t bytes(size_type size) noexcept
  {
    size_t const embedded_literals = std::extent_v<decltype(m_literals)>;
    size_t const additional_literals = (size >= embedded_literals) ? (size - embedded_literals) : 0;
    size_t const total_bytes = sizeof(Clause) + sizeof(Lit) * additional_literals;
    return total_bytes;
  }

  /// Allocate a clause with enough space for 'size' literals.
  static Clause* create(size_type size)
  {
    void* p = subsat_alloc(bytes(size));
    return new (p) Clause{size};
  }

  // static void* operator new(size_t, size_type num_literals)
  // {
  //   size_t const contained_literals = std::extent_v<decltype(m_literals)>;
  //   size_t const additional_literals = std::max(0, static_cast<size_t>(num_literals) - contained_literals);
  //   size_t const total_bytes = sizeof Clause + sizeof Lit * additional_literals;
  //   return ::operator new(total_bytes);
  // }

private:
  // NOTE: do not use this constructor directly
  // because it does not allocate enough memory for the literals
  Clause(size_type size) noexcept
      : m_size{size}
  {
  }

  // cannot copy/move because of flexible array member
  Clause(Clause&) = delete;
  Clause(Clause&&) = delete;
  Clause& operator=(Clause&) = delete;
  Clause& operator=(Clause&&) = delete;

  friend class AllocatedClause;

private:
  size_type m_size;    // number of literals
  Lit m_literals[2];  // actual size is m_size, but C++ does not officially support flexible array members (as opposed to C)
}; // Clause


std::ostream& operator<<(std::ostream& os, Clause const& c)
{
  os << "{ ";
  bool first = true;
  for (Lit lit : c) {
    if (first) {
      first = false;
    } else {
      os << ", ";
    }
    os << lit;
  }
  os << " }";
  return os;
}


// TODO: the current way of using ClauseRefs doesn't make sense. In fact, we're doing additional indirections compared to using pointers.
//       What we need is in-place allocation in a vector<uint32_t>, like kitten does.  (maybe a vector<char> would be better?)  (what about alignment?)
using ClauseRef = uint32_t;  // TODO: make this a struct, with a function to check validity? (operator bool?)
#define InvalidClauseRef (std::numeric_limits<ClauseRef>::max())
using Level = uint32_t;
#define InvalidLevel (std::numeric_limits<Level>::max())

struct VarInfo {
  Level level;
  ClauseRef reason;
};

struct Watch {
  // TODO: optimizations: binary clause, blocking literal
  ClauseRef clause;
};


using Mark = unsigned char;
static constexpr Mark MarkSeen = 1;
static constexpr Mark MarkPoisoned = 2;
static constexpr Mark MarkRemovable = 4;
// enum class Mark : char {
//   Seen = 1,
//   Poisoned = 2,
//   Removable = 4,
// };


class AllocatedClause
{
public:
  void push(Lit lit)
  {
    assert(m_clause);
    assert(m_clause->m_size < m_capacity);
    m_clause->m_literals[m_clause->m_size] = lit;
    m_clause->m_size += 1;
  }

  Clause* build()
  {
    assert(m_clause);
    Clause* c = m_clause;
#ifndef NDEBUG
    m_clause = nullptr;
#endif
    return c;
  }

private:
  AllocatedClause(Clause* clause, uint32_t capacity)
      : m_clause{clause}, m_capacity{capacity}
  {
    assert(m_clause);
  }

  friend class Solver;

private:
  Clause* m_clause;
#ifndef NDEBUG
  uint32_t m_capacity;
#endif
};


class Solver
{
public:
  /// Ensure space for a new variable and return it.
  /// By default, memory is increased exponentially (relying on the default behaviour of std::vector).
  /// Use reserve_variables if you know the number of variables upfront.
  [[nodiscard]] Var new_variable()
  {
    m_unassigned_vars++;
    m_vars.push_back({ .level = InvalidLevel, .reason = InvalidClauseRef});
    m_marks.push_back(0);
    m_values.push_back(Value::Unassigned); // value of positive literal
    m_values.push_back(Value::Unassigned); // value of negative literal
    m_watches.emplace_back();           // positive literal watches
    m_watches.emplace_back();           // negative literal watches
    return Var{m_used_vars++};
  }

  /// Reserve space for n variables (in total).
  void reserve_variables(uint32_t count)
  {
    m_values.reserve(2 * count);
    // TODO: call reserve on all necessary vectors where this is necessary
  }


  AllocatedClause alloc_clause(uint32_t capacity)
  {
    // TODO: allocate clause of given size in the internal storage,
    // but do not yet call add_clause.
  }

    /*
  void add_empty_clause()
  {
  }

  void add_unit_clause(Lit* lit)
  {
  }

  void add_binary_clause(Lit* lit1, Lit* lit2)
  {
  }
  */

  void add_clause(Clause* clause)
  {
    // TODO
    ClauseRef cr = m_clauses.size();
    CDEBUG("add_clause: " << cr << " ~> " << *clause);
    m_clauses.push_back(clause);
    watch_clause(cr);
  }

  Result solve()
  {
    m_trail.reserve(m_used_vars);

    if (m_inconsistent) {
      return Result::Unsat;
    }

    // propagate_units();  // TODO do this later when we add optimizations

    while (true) {
      ClauseRef conflict = propagate();

      assert(checkInvariants());

      if (conflict != InvalidClauseRef) {
        if (!analyze(conflict)) {
          return Result::Unsat;
        }
      } else {
        if (m_unassigned_vars == 0) {
          return Result::Sat;
        } else {
          // TODO: restart? switch mode? reduce clause db?
          decide();
        }
      }
    }
  }

private:
  Clause const& get_clause(ClauseRef ref) const
  {
    assert(ref != InvalidClauseRef);
    assert(ref < m_clauses.size());
    return *m_clauses[ref];
  }

  Clause& get_clause(ClauseRef ref)
  {
    return const_cast<Clause&>(std::as_const(*this).get_clause(ref));
  }

  /// Set the literal to true.
  /// Precondition: literal is not assigned.
  void assign(Lit lit, ClauseRef reason)
  {
    CDEBUG("assign: " << lit << ", reason: " << reason);
    // TODO: log

    /*
    // TODO: Assignment on root level => no need to store the reason
    // (done in satch, but not in kitten)
    if (m_level == 0) {
      reason = InvalidClauseRef;
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

  void propagate_units()
  {
    for (Lit lit : m_units) {
      assign(lit, InvalidClauseRef);
    }
  }

  /// Make a decision.
  void decide()
  {
    CDEBUG("decide");
    assert(m_unassigned_vars > 0);
    assert(!m_inconsistent);
    assert(m_level < m_used_vars);

    m_level += 1;

    // TODO: use VMTF heuristic
    // for now, just choose the first unassigned literal
    for (uint32_t lit_idx = 0; lit_idx < m_values.size(); ++lit_idx) {
      Lit const lit = Lit::from_index(lit_idx);
      if (m_values[lit] == Value::Unassigned) {
        assign(lit, InvalidClauseRef);
        return;
      }
    }
    assert(false);
  }

  /// Unit propagation.
  /// Returns the conflicting clause when a conflict is encountered,
  /// or InvalidClauseRef if all unit clauses have been propagated without conflict.
  ClauseRef propagate()
  {
    CDEBUG("propagate");
    // assert(checkInvariants());
    while (m_propagate_head < m_trail.size()) {
      Lit const lit = m_trail[m_propagate_head++];
      ClauseRef const conflict = propagate_literal(lit);
      if (conflict != InvalidClauseRef) {
        return conflict;
      }
    }
    return InvalidClauseRef;
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

    ClauseRef conflict = InvalidClauseRef;

    while (conflict == InvalidClauseRef && p != watches.cend()) {
      Watch const& watch = *p;
      *q++ = *p++;  // keep the watch by default

      // TODO: binary clause optimization
      // if (p->binary) {
      // ...
      // } else {
      // ... (current code here)
      // }

      // TODO: blocking literal optimization

      ClauseRef const clause_ref = watch.clause;
      Clause& clause = get_clause(clause_ref);
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
        // TODO: think about why this works. (if replacement was assigned after not_lit, it must still have been in the same decision level? so when we backtrack, we're guaranteed to undo both.)
        assert(m_vars[replacement.var()].level == m_vars[not_lit.var()].level);
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
        conflict = watch.clause;
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
    m_watches[lit].push_back(Watch{ .clause = clause_ref });
  }

  /// Watch first to literals in the clause.
  void watch_clause(ClauseRef clause_ref)
  {
    Clause const& clause = get_clause(clause_ref);
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

    // assert(conflict_ref != InvalidClauseRef);
    // Clause const& conflict = get_clause(conflict_ref);

    Level const conflict_level = m_level;
    if (conflict_level == 0) {
      // Conflict on root level
      m_inconsistent = true;
      return false;
    }

    // TODO: move to member variable (reduce allocation overhead)
    std::vector<Lit> clause;  // the learned clause
    std::vector<Level> blocks;  // analyzed decision levels
    std::vector<Var> seen;  // analyzed literals
    ivector<Level, char> frames; // stores for each level whether we already have it in blocks; NOTE: should be bool, but C++ vector<bool> is bad
    frames.resize(conflict_level, 0);
    assert(clause.empty());
    assert(blocks.empty());
    assert(seen.empty());
    assert(frames.size() >= conflict_level);
    assert(std::all_of(frames.cbegin(), frames.cend(), [](auto x){ return x == 0; }));

    // Make room for the first UIP
    clause.push_back(Lit::invalid());

    auto t = m_trail.crbegin();
    uint32_t unresolved_on_current_level = 0;
    Lit uip = Lit::invalid();
    ClauseRef reason_ref = conflict_ref;

    while (true) {
      CDEBUG("reason_ref = " << reason_ref);
      assert(reason_ref != InvalidClauseRef);
      Clause const& reason = get_clause(reason_ref);

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
          unresolved_on_current_level++;
        }
      }  // for (lit : reason)

      // Find next literal to resolve by going backward over the trail
      do {
        assert(t < m_trail.crend());
        uip = *t;
        t++;
      } while (!m_marks[uip.var()]);

      unresolved_on_current_level--;
      if (unresolved_on_current_level == 0) {
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

    // TODO: sort analyzed vars by time stamp
    for (Var var : seen) {
      // TODO: bump in varorder
      assert(m_marks[var]);
      m_marks[var] = 0;
    }
    seen.clear();

    backtrack(jump_level);

    uint32_t const size = clause.size();
    assert(size > 0);
    if (size == 1) {
      // We learned a unit clause
      assert(jump_level == 0);
      CDEBUG("learned unit: " << not_uip);
      assign(not_uip, InvalidClauseRef);
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

      Clause* learned = Clause::create(size);
      for (uint32_t i = 0; i < size; ++i) {
        (*learned)[i] = clause[i];
      }
      ClauseRef learned_ref = m_clauses.size();
      CDEBUG("learned: " << learned_ref << " ~> " << *learned);
      m_clauses.push_back(learned);  // TODO: call new_redundant_clause
      watch_clause(learned_ref);
      assign(not_uip, learned_ref);
    }

    clause.clear();

    return true;
  }  // analyze

  void backtrack(Level new_level)
  {
    CDEBUG("backtrack to level " << new_level);
    assert(new_level <= m_level);

    // TODO: update VMTF

    while (!m_trail.empty()) {
      Lit const lit = m_trail.back();

      if (get_level(lit) == new_level) {
        break;
      }

      m_trail.pop_back();
      assert(m_unassigned_vars < m_used_vars);
      m_unassigned_vars += 1;
      assert(m_values[lit] == Value::True);
      assert(m_values[~lit] == Value::False);
      m_values[lit] = Value::Unassigned;
      m_values[~lit] = Value::Unassigned;
    }

    m_propagate_head = m_trail.size();
    m_level = new_level;
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
  ivector<Lit, Value> m_values;

  /// Decision levels and reasons of variables
  ivector<Var, VarInfo> m_vars;

  /// Mark flags of variables
  ivector<Var, Mark> m_marks;

  ivector<ClauseRef, Clause*> m_clauses;
  std::vector<Lit> m_units;
  ivector<Lit, std::vector<Watch>> m_watches;

  std::vector<Lit> m_trail;  ///< Currently true literals in order of assignment; TODO: pre-allocate to #variables
  uint32_t m_propagate_head = 0; // index into trail, the next literal to propagate

  // std::vector<Clause*> clauses;
}; // Solver


// TODO:
// 1. basic implementation of CDCL with only major stuff like learning and 2-watched-literals without further complications
// 2. add optimizations as desired


} // namespace SMTSubsumption

#endif /* !SUBSAT_HPP */
