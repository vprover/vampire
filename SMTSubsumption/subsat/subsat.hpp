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
#include <vector>

#include "ivector.hpp"

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

using std::uint32_t;

enum class Value : signed char {
  False = -1,
  Unknown = 0,   // TODO: rename to Unassigned
  True = 1,
};

Value operator~(Value v) {
  return static_cast<Value>(-static_cast<signed char>(v));
}


class Lit;

/// Boolean variable represented by its integer index.
/// Use consecutive indices starting at 0.
class Var final {
  uint32_t m_index;

public:
  explicit constexpr Var(uint32_t index) noexcept
      : m_index{index}
  {
    // assert(m_index <= Var::max_index());  // TODO: how to assert in constexpr constructor?
  }

  [[nodiscard]] constexpr uint32_t index() const noexcept
  {
    return m_index;
  }

  [[nodiscard]] static constexpr uint32_t max_index() noexcept
  {
    return (1u << 31) - 2;
  }

  [[nodiscard]] static constexpr Var invalid() noexcept
  {
    return Var{std::numeric_limits<uint32_t>::max()};
  }

  [[nodiscard]] constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  [[nodiscard]] constexpr Lit operator~() const noexcept;
  [[nodiscard]] constexpr operator Lit() const noexcept;
}; // Var

static_assert(Var::max_index() == static_cast<uint32_t>(INT32_MAX - 1), "unexpected max variable index");
static_assert(Var::max_index() < Var::invalid().index(), "valid variable indices overlap with invalid sentinel value");

[[nodiscard]] constexpr bool operator==(Var lhs, Var rhs) noexcept
{
  return lhs.index() == rhs.index();
}

[[nodiscard]] constexpr bool operator!=(Var lhs, Var rhs) noexcept
{
  return !operator==(lhs, rhs);
}

[[nodiscard]] constexpr bool operator<(Var lhs, Var rhs) noexcept
{
  return lhs.index() < rhs.index();
}


/// Boolean literals represented by integer index.
/// The least significant bit indicates the sign.
///
/// Mapping from variable indices to literal indices:
///    Lit{0} ... 0
///   ~Lit{0} ... 1
///    Lit{1} ... 2
///   ~Lit{1} ... 3
///      :
///      :
class Lit final {
  uint32_t m_index;

private:
  friend class Clause;
  /// Uninitialized value (for clause constructor)
  Lit() noexcept
  // : m_index{Lit::invalid().index()}
  {
  }

  explicit constexpr Lit(uint32_t index) noexcept
      : m_index{index}
  {
    // assert(m_index <= Lit::max_index()); // TODO: how to assert in constexpr constructor?
  }

public:
  explicit constexpr Lit(Var var, bool positive) noexcept
      : Lit{2 * var.index() + static_cast<uint32_t>(!positive)}
  {
  }

  [[nodiscard]] static constexpr Lit from_index(uint32_t index) noexcept
  {
    assert(index <= Lit::max_index());
    return Lit{index};
  }

  [[nodiscard]] static constexpr Lit pos(Var var) noexcept
  {
    return Lit{var, true};
  }

  [[nodiscard]] static constexpr Lit neg(Var var) noexcept
  {
    return Lit{var, false};
  }

  [[nodiscard]] constexpr uint32_t index() const noexcept
  {
    return m_index;
  }

  [[nodiscard]] static constexpr uint32_t max_index() noexcept
  {
    static_assert(Var::max_index() < (std::numeric_limits<uint32_t>::max() - 1) / 2, "cannot represent all literals");
    return 2 * Var::max_index() + 1;
  }

  [[nodiscard]] static constexpr Lit invalid() noexcept
  {
    return Lit{std::numeric_limits<uint32_t>::max()};
  }

  [[nodiscard]] constexpr bool is_valid() const noexcept
  {
    return m_index <= max_index();
  }

  [[nodiscard]] constexpr bool is_positive() const noexcept
  {
    return (m_index & 1) == 0;
  }

  [[nodiscard]] constexpr bool is_negative() const noexcept
  {
    return !is_positive();
  }

  [[nodiscard]] constexpr Lit operator~() const noexcept
  {
    return Lit{m_index ^ 1};
  }

  [[nodiscard]] constexpr Var var() const noexcept
  {
    return Var{m_index / 2};
  }
}; // Lit

static_assert(Lit::max_index() < Lit::invalid().index(), "valid literal indices overlap with invalid sentinel value");



[[nodiscard]] constexpr bool operator==(Lit lhs, Lit rhs) noexcept
{
  return lhs.index() == rhs.index();
}

[[nodiscard]] constexpr bool operator!=(Lit lhs, Lit rhs) noexcept
{
  return !operator==(lhs, rhs);
}




[[nodiscard]] constexpr Lit Var::operator~() const noexcept
{
  return Lit{*this, false};
}

[[nodiscard]] constexpr Var::operator Lit() const noexcept
{
  return Lit{*this, true};
}





inline void* subsat_alloc(std::size_t size)
{
#ifdef SUBSAT_STANDALONE
  void* p = std::malloc(size);
#else
  void* p = ALLOC_UNKNOWN(size, "subsat");
#endif
  if (!p && size > 0) {
    throw std::bad_alloc();
  }
  return p;
}

inline void subsat_dealloc(void* p)
{
#ifdef SUBSAT_STANDALONE
  std::free(p);
#else
  DEALLOC_UNKNOWN(p, "subsat");
#endif
}






class Clause final {
public:
  using iterator = Lit*;
  using const_iterator = Lit const*;
  using size_type = uint32_t;

  [[nodiscard]] iterator begin() noexcept
  {
    return &m_literals[0];
  }

  [[nodiscard]] iterator end() noexcept
  {
    return begin() + m_size;
  }

  // [[nodiscard]] const_iterator begin() const noexcept
  // {
  //   return &m_literals[0];
  // }

  // [[nodiscard]] const_iterator end() const noexcept
  // {
  //   return begin() + m_size;
  // }

  [[nodiscard]] const_iterator cbegin() const noexcept
  {
    return &m_literals[0];
  }

  [[nodiscard]] const_iterator cend() const noexcept
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

private:
  size_type m_size;    // number of literals
  Lit m_literals[2];  // actual size is m_size, but C++ does not officially support flexible array members (as opposed to C)
}; // Clause


template <> struct DefaultIndex<Var> {
  using type = IndexMember<Var>;
};
template <> struct DefaultIndex<Lit> {
  using type = IndexMember<Lit>;
};


enum class Result {
  Sat = 10,
  Unsat = 20,
};

std::ostream& operator<<(std::ostream& os, Result r)
{
  switch (r) {
    case Result::Sat:
      os << "satisfiable";
      break;
    case Result::Unsat:
      os << "unsatisfiable";
      break;
  }
  return os;
}




using ClauseRef = uint32_t;  // TODO: make this a struct, with a function to check validity? (operator bool?)
using Level = uint32_t;
#define InvalidClauseRef (std::numeric_limits<ClauseRef>::max())

struct VarInfo {
  Level level;
  ClauseRef reason;
};

struct Watch {
  // TODO: optimizations: binary clause, blocking literal
  ClauseRef clause;
};



class Solver {
public:

  /// Ensure space for a new variable and return it.
  [[nodiscard]] Var new_variable()
  {
    reserve_variables(1);
    return Var{m_used_vars++};
  }

  /// Reserve space for n additional variables.
  void reserve_variables(uint32_t count)
  {
    if (m_used_vars + count <= m_allocated_vars) {
      return;
    }
    m_allocated_vars = m_used_vars + count;
    m_values.reserve(2 * m_allocated_vars);
    // TODO
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
  }

  Result solve()
  {

    if (m_inconsistent) {
      return Result::Unsat;
    }

    // propagate_units();  // TODO do this later when we add optimizations

    while (true) {
      ClauseRef conflict = propagate();
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
  Clause* get_clause(ClauseRef ref)
  {
    assert(ref != InvalidClauseRef);
    assert(ref < m_clauses.size());
    return m_clauses[ref];
  }

  /// Set the literal to true.
  /// Precondition: literal is not assigned.
  void assign(Lit lit, ClauseRef reason)
  {
    // TODO: log

    /*
    // TODO: Assignment on root level => no need to store the reason
    // (done in satch, but not in kitten)
    if (m_level == 0) {
      reason = InvalidClauseRef;
    } */

    // TODO: kitten does phase-saving as well

    // precondition: not assigned
    assert(m_values[lit] == Value::Unknown);
    assert(m_values[~lit] == Value::Unknown);

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
    // TODO
  }

  /// Unit propagation.
  /// Returns the conflicting clause when a conflict is encountered,
  /// or InvalidClauseRef if all unit clauses have been propagated without conflict.
  ClauseRef propagate()
  {
    while (m_propagate_head < m_trail.size()) {
      // p is the next literal to be propagated
      Lit const lit = m_trail[m_propagate_head];
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
    assert(checkInvariants());
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
      Clause& clause = *get_clause(clause_ref);
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
      else if (replacement_value == Value::Unknown) {
        // The replacement literal is unassigned.
        // Unwatch not_lit
        --q;
        // Swap watched literal with its replacement
        clause[1] = replacement;
        *replacement_it = not_lit;
        // Watch the replacement literal
        watch_literal(replacement, /* TODO: other_lit, */ clause_ref);
      }
      else if (other_value != Value::Unknown) {
        // All literals in the clause are false => conflict
        assert(other_value == Value::False);
        conflict = watch.clause;
      }
      else {
        // All literals except other_lit are false => propagate
        assert(other_value == Value::Unknown);
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


  /// Analyze conflict, learn a clause, backjump.
  /// Returns true if the search should continue.
  bool analyze(ClauseRef conflict_ref)
  {
    assert(conflict_ref != InvalidClauseRef);
    Clause* conflict = get_clause(conflict_ref);
    // TODO
  }

  void backtrack(Level new_level)
  {
    assert(new_level <= m_level);
    // TODO
  }

#ifndef NDEBUG
  [[nodiscard]] bool checkInvariants() const
  {
    // assigned vars + unassiged vars = used vars
    assert(m_trail.size() + m_unassigned_vars == m_used_vars);

    // Every variable is at most once on the trail
    std::set<Var> trail_vars;
    for (Lit lit : m_trail) {
      auto [_, inserted] = trail_vars.insert(lit.var());
      assert(inserted);
    }
    assert(trail_vars.size() == m_trail.size());
    assert(m_trail.size() <= m_used_vars);

    // TODO: (after optimizations) Every stored clause has size >= 3

    // TODO: watch invariants
    // 1. status of watch literals
    // 2. watched literals are always the first two
    // 3. every clause in m_clauses is watched (?) [may not work with deletion?]

    return true;
  }
#endif

private:
  bool m_inconsistent;
  uint32_t m_used_vars;
  uint32_t m_allocated_vars;
  uint32_t m_unassigned_vars; ///< Number of variables that have not yet been assigned

  /// Current decision level
  Level m_level;

  /// Current assignment of literals.
  /// We store the value for both literal polarities to make the lookup simpler and branchless.
  ivector<Lit, Value> m_values;

  /// Decision levels and reasons of variables
  ivector<Var, VarInfo> m_vars;

  ivector<ClauseRef, Clause*> m_clauses;
  std::vector<Lit> m_units;
  ivector<Lit, std::vector<Watch>> m_watches;

  std::vector<Lit> m_trail;  ///< Currently true literals in order of assignment; TODO: pre-allocate to #variables
  uint32_t m_propagate_head;  // index into trail, the next literal to propagate

  // std::vector<Clause*> clauses;
}; // Solver


// TODO:
// 1. basic implementation of CDCL with only major stuff like learning and 2-watched-literals without further complications
// 2. add optimizations as desired


} // namespace SMTSubsumption

#endif /* !SUBSAT_HPP */
