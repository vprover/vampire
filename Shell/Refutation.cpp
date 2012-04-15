/**
 * @file Refutation.cpp
 * Implements the class for printing refutations
 * @since 04/01/2008 Torrevieja
 */

#include "Debug/Tracer.hpp"

#include "Lib/Hash.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"
#include "Lib/Sort.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Refutation.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Refutation::Refutation(Unit* unit,bool detailed)
  : _goal(unit),
    _detailed(detailed)
{
}

void Refutation::output(ostream& str)
{
  CALL("Refutation::output");

  Stack<Unit*> units;
  Set<Unit*> done;
  units.push(_goal);
  while (! units.isEmpty()) {
    Unit* unit = units.pop();
    if (done.contains(unit)) {
      continue;
    }
    done.insert(unit);
    Inference* inf = unit->inference();
    Inference::Iterator it = inf->iterator();
    while (inf->hasNext(it)) {
      units.push(inf->next(it));
    }
  }
  sort<Refutation,Unit*>(units.begin(),units.end());
  do {
    // str << units.pop()->toString() << "\n";
  }
  while (!units.isEmpty());
} // Refutation::Output

/**
 * Unit comparison using their numbers, required to sort units.
 * @since 04/11/2011 Elba
 */
Comparison Refutation::compare(Unit* u1,Unit* u2)
{
  return u1->number() < u2->number() ? LESS : u1 == u2 ? EQUAL : GREATER;
} // Refutation::compare
