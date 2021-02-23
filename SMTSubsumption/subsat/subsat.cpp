#include "subsat.hpp"

#include <fstream>
#include <initializer_list>
#include <iostream>
#include <string>

using namespace subsat;

#ifdef SUBSAT_STANDALONE

/// DIMACS literals are 1, -1, 2, -2, ...
static Lit from_dimacs(int dimacs_lit)
{
  assert(dimacs_lit != 0);
  int idx = std::abs(dimacs_lit) - 1;
  Var v{static_cast<uint32_t>(idx)};
  return Lit{v, dimacs_lit > 0};
}

static void parse_dimacs(std::istream& in, Solver& solver)
{
  std::string buf;

  in >> buf;
  if (buf != "p") { throw std::runtime_error{"expected: p"}; }
  in >> buf;
  if (buf != "cnf") { throw std::runtime_error{"expected: cnf"}; }

  int expected_vars, expected_clauses;
  in >> expected_vars;
  in >> expected_clauses;

  int parsed_vars = 0;
  int parsed_clauses = 0;
  int dimacs_lit;
  std::vector<Lit> clause_buf;
  while (in >> dimacs_lit) {
    if (std::abs(dimacs_lit) > parsed_vars) {
      parsed_vars = std::abs(dimacs_lit);
    }
    if (dimacs_lit == 0) {
      assert(clause_buf.size() <= UINT32_MAX);
      auto clause_size = static_cast<uint32_t>(clause_buf.size());
      solver.add_clause(clause_buf.data(), clause_size);
      clause_buf.clear();
      parsed_clauses += 1;
    } else {
      clause_buf.push_back(from_dimacs(dimacs_lit));
    }
  }
  if (!clause_buf.empty()) {
    throw std::runtime_error{"expected: literal or 0"};
  }
  if (parsed_vars != expected_vars) {
    throw std::runtime_error{"wrong #variables"};
  }
  if (parsed_clauses != expected_clauses) {
    throw std::runtime_error{"wrong #clauses"};
  }
}

int main(int argc, char* argv[])
{
  Solver s;
  assert(s.empty());

  Result res;

#if 0
  if (argc > 1) {
    char const* program = (argc >= 1) ? argv[0] : "subsat";
    std::cout << "Usage: " << program << std::endl;
    return 1;
  }

  Var x = s.new_variable();
  Var y = s.new_variable();
  Var z = s.new_variable();
  // Var u = s.new_variable();

  std::cout << "\n\nADDING CLAUSES\n" << std::endl;
  // s.add_clause({x, y, z});
  // s.add_clause({x, y, ~z});
  // s.add_clause({x, ~y, z});
  // s.add_clause({x, ~y, ~z});
  // s.add_clause({~x, y, z});
  // s.add_clause({~x, y, ~z});
  // s.add_clause({~x, ~y, z});
  // s.add_clause({~x, ~y, ~z});
  s.add_clause({x, y});
  s.add_clause({y, z});
  s.add_clause({x, z});
  s.add_atmostone_constraint({x, y, z});

  std::cout << "SOLVING..." << std::endl;
  res = s.solve();

  std::cout << "RESULT: " << static_cast<int>(res) << " " << res << std::endl;

#else

  if (argc < 2) {
    char const* program = (argc >= 1) ? argv[0] : "subsat";
    std::cout << "Usage: " << program << " FILE..." << std::endl;
    return 1;
  }

  for (int i = 1; i < argc; ++i) {
    std::string filename{argv[i]};

    s.clear();

    std::cout << "INPUT " << filename << std::endl;
    if (filename == "-") {
      parse_dimacs(std::cin, s);
    } else {
      std::ifstream file_in{filename};
      parse_dimacs(file_in, s);
    }

    std::cout << "SOLVING..." << std::endl;
    res = s.solve();

    std::cout << "RESULT " << filename << ": " << static_cast<int>(res) << " " << res << std::endl;
  }

#endif

  return static_cast<int>(res);
}
#endif



#ifndef NDEBUG
bool Solver::checkEmpty() const
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
  assert(std::all_of(m_watches.begin(), m_watches.end(), [](std::vector<Watch> const& ws){ return ws.empty(); }));
  assert(std::all_of(m_watches_amo.begin(), m_watches_amo.end(), [](std::vector<Watch> const& ws){ return ws.empty(); }));
  assert(m_trail.empty());
  assert(m_propagate_head == 0);
  assert(tmp_analyze_clause.empty());
  assert(tmp_analyze_blocks.empty());
  assert(tmp_analyze_seen.empty());
  assert(m_frames.empty());
  return true;
}

bool Solver::checkInvariants() const
{
  // assigned vars + unassiged vars = used vars
  assert(m_trail.size() + m_unassigned_vars == m_used_vars);

  assert(m_values.size() == 2 * m_used_vars);

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

  // Check clause invariants
  for (ClauseRef cr : m_clauses) {
    if (cr == tmp_binary_clause_ref) {
      continue;
    }
    Clause const& clause = m_clauses.deref(cr);
    // No duplicate variables in the clause (this prevents duplicate literals and tautological clauses)
    std::set<Var> clause_vars;
    for (Lit lit : clause) {
      assert(lit.is_valid());
      bool inserted = clause_vars.insert(lit.var()).second;
      assert(inserted);
    }
    assert(clause_vars.size() == clause.size());
  }

  // Check watch invariants if we're in a fully propagated state
  if (m_propagate_head == m_trail.size()) {
    assert(checkWatches());
  }

  return true;
}  // checkInvariants

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
  /*
  // Every clause of size >= 2 is watched twice
  // NOTE: not true atm because we also store atmostone constraints in the same space
  for (ClauseRef cr : m_clauses) {
    Clause const& c = m_clauses.deref(cr);
    if (c.size() >= 2) {
      auto it = num_watches.find(cr.index());
      assert(it != num_watches.end());
      assert(it->second == 2);
      num_watches.erase(it);
    }
  }
  assert(num_watches.empty());
  */
  return true;
}
#endif

#if LOGGING_ENABLED
void Solver::showAssignment(std::ostream& os) const
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
#endif




Result Solver::solve()
{
  m_trail.reserve(m_used_vars);
  m_frames.resize(m_used_vars + 1, 0);
  m_queue.resize_and_init(m_used_vars);
  assert(m_queue.checkInvariants(m_values));

  if (!tmp_binary_clause_ref.is_valid()) {
    auto ca = m_clauses.alloc(2);
    ca.push(Lit::invalid());
    ca.push(Lit::invalid());
    tmp_binary_clause_ref = ca.build();
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
        return Result::Sat;
      } else {
        // TODO: restart? switch mode? reduce clause db?
        decide();
      }
    }
  }
}
