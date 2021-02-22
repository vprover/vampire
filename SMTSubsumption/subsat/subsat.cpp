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
  if (argc < 2) {
    char const* program = (argc >= 1) ? argv[0] : "subsat";
    std::cout << "Usage: " << program << " FILE..." << std::endl;
    return 1;
  }

  Solver s;
  Result res;

  // Var x = s.new_variable();
  // Var y = s.new_variable();
  // Var z = s.new_variable();

  // std::cout << "\n\nADDING CLAUSES\n" << std::endl;
  // s.add_clause({x, y, z});
  // s.add_clause({x, y, ~z});
  // s.add_clause({x, ~y, z});
  // s.add_clause({x, ~y, ~z});
  // s.add_clause({~x, y, z});
  // s.add_clause({~x, y, ~z});
  // s.add_clause({~x, ~y, z});
  // s.add_clause({~x, ~y, ~z});

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

  return static_cast<int>(res);
}
#endif



#ifndef NDEBUG
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

/*
  // Check clause invariants
  for (Clause const* clause : m_clauses) {
    // Every stored clause has size >= 2
    // TODO: after binary clause optimization: >= 3
    assert(clause->size() >= 2);
    // No duplicate variables in the clause (this prevents duplicate literals and tautological clauses)
    std::set<Var> clause_vars;
    for (Lit lit : *clause) {
      assert(lit.is_valid());
      auto [_, inserted] = clause_vars.insert(lit.var());
      assert(inserted);
    }
    assert(clause_vars.size() == clause->size());
  }
  */

  // Check watch invariants
  // assert(m_watches.size() == 2 * m_used_vars);  // not true because we keep those after clear()
  std::map<ClauseRef::index_type, int> num_watches; // counts how many times each clause is watched
  for (uint32_t lit_idx = 0; lit_idx < m_watches.size(); ++lit_idx) {
    Lit const lit = Lit::from_index(lit_idx);
    for (Watch watch : m_watches[lit]) {
      num_watches[watch.clause_ref.index()] += 1;
      Clause const& clause = m_clauses.deref(watch.clause_ref);
      // The watched literals are always the first two in the clause
      assert(clause[0] == lit || clause[1] == lit);
      // Check status of watch literals
      // TODO: this holds only after propagation (obviously); so maybe we should make it a separate check.
      bool clause_satisfied =
        std::any_of(clause.begin(), clause.end(), [this](Lit l){ return m_values[l] == Value::True; });
      if (clause_satisfied) {
        Level min_true_level = std::numeric_limits<Level>::max();
        for (Lit l : clause) {
          if (m_values[l] == Value::True && get_level(l) < min_true_level) {
            min_true_level = get_level(l);
          }
        }
        // If the clause is satisfied and the watches are assigned,
        // one of the watches must be on the same level or above one of the true literals.
        bool both_watches_unassigned =
          m_values[clause[0]] == Value::Unassigned && m_values[clause[1]] == Value::Unassigned;
        assert(both_watches_unassigned || get_level(clause[0]) >= min_true_level || get_level(clause[1]) >= min_true_level);
      } else {
        // If the clause is not satisfied, either both watch literals must be unassigned,
        // or all literals are false (conflict).
        bool both_watches_unassigned =
          m_values[clause[0]] == Value::Unassigned && m_values[clause[1]] == Value::Unassigned;
        bool is_conflict =
          std::all_of(clause.begin(), clause.end(), [this](Lit l){ return m_values[l] == Value::False; });
        // TODO fix this
        // assert(both_watches_unassigned || is_conflict);  // ???
        (void)is_conflict;
        (void)both_watches_unassigned;
      }
    }
  }
  // Every clause in m_clauses is watched twice
  // for (ClauseRef::index_type cr = 0; cr < m_clauses.size(); ++cr) {
  //   assert(num_watches[cr] == 2);
  // }
  for (auto kvpair : num_watches) {
    assert(kvpair.second == 2);
  }

  return true;
}
#endif




Result Solver::solve()
{
  m_trail.reserve(m_used_vars);
  m_frames.resize(m_used_vars + 1, 0);
  m_queue.resize_and_init(m_used_vars);
  assert(m_queue.checkInvariants(m_values));

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
