#include "subsat.hpp"

#include <fstream>
#include <initializer_list>
#include <iostream>
#include <string>

using namespace subsat;

#if SUBSAT_STANDALONE

/// DIMACS literals are 1, -1, 2, -2, ...
static Lit from_dimacs(int dimacs_lit)
{
  assert(dimacs_lit != 0);
  int idx = std::abs(dimacs_lit) - 1;
  Var v{static_cast<uint32_t>(idx)};
  return Lit{v, dimacs_lit > 0};
}

template <template <typename> class A>
static void parse_dimacs(std::istream& in, Solver<A>& solver)
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
  Solver<> s;
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

  s.add_clause({x, y, z});
  s.add_clause({x, y, ~z});
  s.add_clause({x, ~y, z});
  s.add_clause({x, ~y, ~z});
  s.add_clause({~x, y, z});
  s.add_clause({~x, y, ~z});
  s.add_clause({~x, ~y, z});
  s.add_clause({~x, ~y, ~z});
  s.add_clause({~x, ~y, ~z, ~z, ~y, ~z});
  s.add_clause({~x, ~y, ~z, ~z, y, ~z});

  // s.add_clause({x, y});
  // s.add_clause({y, z});
  // s.add_clause({x, z});
  // s.add_atmostone_constraint({x, y, z});

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

#endif  // SUBSAT_STANDALONE
