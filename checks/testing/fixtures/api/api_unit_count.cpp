/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

/*
 * Isolated API probe for the cached clause count in Problem::addUnits.
 * Compiled and linked beside a completed upstream Debug build.
 */
#include <cstdlib>
#include <iostream>

#include "Test/UnitTesting.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Shell/Property.hpp"

using namespace Kernel;

TEST_FUN(only_incoming_units_count_once)
{
  Problem problem;
  auto first = Clause::fromLiterals({}, FromInput(UnitInputType::AXIOM));
  problem.addUnits(new UnitList(first));
  const auto before = problem.getProperty()->clauses();

  auto second = Clause::fromLiterals({}, FromInput(UnitInputType::AXIOM));
  problem.addUnits(new UnitList(second));
  const auto after = problem.getProperty()->clauses();
  unsigned actualUnits = 0;
  UnitList::Iterator units(problem.units());
  while (units.hasNext()) {
    units.next();
    ++actualUnits;
  }

  std::cout << "F13_COUNT before=" << before
            << " cached_after=" << after
            << " actual_units=" << actualUnits
            << " expected_after=2" << std::endl;

  UnitList::destroy(problem.units());
  problem.units() = nullptr;
  first->destroy();
  second->destroy();
  if (before != 1 || after != 2 || actualUnits != 2) {
    std::exit(1);
  }
}
