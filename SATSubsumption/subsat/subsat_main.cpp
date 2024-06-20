/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
#include "./subsat.hpp"

#include <cassert>
#include <fstream>
#include <initializer_list>
#include <iostream>
#include <string>

using namespace subsat;

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

static void parse_input(std::string filename, Solver& solver)
{
    if (filename == "-") {
      parse_dimacs(std::cin, solver);
    } else {
      std::ifstream file_in{filename};
      parse_dimacs(file_in, solver);
    }
}

static int enumerate_models(std::string filename)
{
  if (filename == "-") {
    std::cerr << "stdin not supported for model enumeration at the moment!" << std::endl;
    return 2;
  }

  Solver s;
  parse_input(filename, s);

  // Collect all models
  std::vector<std::vector<Lit>> models;
  Result res;
  while ((res = s.solve()) == Result::Sat) {
    models.push_back({});
    auto& model = models.back();
    s.get_model(model);
    // std::cout << ShowVec(model) << std::endl;
  }
  if (res != Result::Unsat) {
    std::cerr << "Enumerating models: unexpected result: " << res << std::endl;
    return 1;
  }

  // Check that the enumeration procedure didn't miss any models
  s.clear();
  parse_input(filename, s);
  // Add blocking clause for each model discovered in the previous run
  for (auto const& model : models) {
    s.constraint_start();
    for (Lit lit : model) {
      s.constraint_push_literal(~lit);
    }
    auto handle = s.constraint_end();
    s.add_clause(handle);
  }
  // We expect unsat, otherwise we missed some model in the first part.
  if ((res = s.solve()) != Result::Unsat) {
    std::cerr << "Checking: unexpected result: " << res << std::endl;
    return 1;
  }

  return 0;
}

int main(int argc, char* argv[])
{
  Solver s;
  assert(s.empty());

  print_config(std::cout);

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

  (void)enumerate_models;  // suppress 'unused function' warning
  // return enumerate_models(argv[1]);

  for (int i = 1; i < argc; ++i) {
    std::string filename{argv[i]};

    s.clear();

    std::cout << "INPUT " << filename << std::endl;
    parse_input(filename, s);

    std::cout << "SOLVING..." << std::endl;
    res = s.solve();

    std::cout << "RESULT " << filename << ": " << static_cast<int>(res) << " " << res << std::endl;
  }

#endif

  return static_cast<int>(res);
}
