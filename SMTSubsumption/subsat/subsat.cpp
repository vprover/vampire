#include "subsat.hpp"

#include <initializer_list>
#include <iostream>

using namespace SMTSubsumption;

#ifdef SUBSAT_STANDALONE

Clause* make_clause(std::initializer_list<Lit> literals)
{
  Clause* cl = Clause::create(literals.size());
  for (size_t i = 0; i < literals.size(); ++i) {
    (*cl)[i] = literals.begin()[i];
  }
  return cl;
}

void add_clause(Solver& solver, std::initializer_list<Lit> literals)
{
  solver.add_clause(make_clause(literals));
}

int main()
{
    std::cout << "hello" << std::endl;

    Solver s;
    Var x = s.new_variable();
    Var y = s.new_variable();
    Var z = s.new_variable();

    s.add_clause(make_clause({x, y, z}));
    s.add_clause(make_clause({x, y, ~z}));
    s.add_clause(make_clause({x, ~y, z}));
    s.add_clause(make_clause({x, ~y, ~z}));
    s.add_clause(make_clause({~x, y, z}));
    s.add_clause(make_clause({~x, y, ~z}));
    s.add_clause(make_clause({~x, ~y, z}));
    s.add_clause(make_clause({~x, ~y, ~z}));

    auto res = s.solve();

    std::cout << "Result: " << res << std::endl;

    return 0;
}
#endif
