
/*
 * File Refutation.cpp.
 *
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 *
 * In summary, you are allowed to use Vampire for non-commercial
 * purposes but not allowed to distribute, modify, copy, create derivatives,
 * or use in competitions. 
 * For other uses of Vampire please contact developers for a different
 * licence, which we will make an effort to provide. 
 */
/**
 * @file Refutation.cpp
 * Implements the class for printing refutations
 * @since 04/01/2008 Torrevieja
 */

#include "Debug/Tracer.hpp"

#include "Lib/Hash.hpp"
#include "Lib/Set.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Inference.hpp"

#include "Refutation.hpp"

using namespace Lib;
using namespace Kernel;
using namespace Shell;

Refutation::Refutation(Unit* unit,bool detailed)
  : _goal(unit)/*,
    _detailed(detailed) MS: unused */
{
}

void Refutation::output(ostream& str)
{
  CALL("Refutation::output");

  Stack<Unit*> units(128);
  Set<Unit*,Refutation> done;

  units.push(_goal);
  while (! units.isEmpty()) {
    Unit* unit = units.pop();
    if (done.contains(unit)) {
      continue;
    }
    done.insert(unit);
    str << unit->toString() << "\n";
    Inference* inf = unit->inference();
    Inference::Iterator it = inf->iterator();
    while (inf->hasNext(it)) {
      units.push(inf->next(it));
    }
  }
} // Refutation::Output

/** hash function, required for hashing units */
unsigned Refutation::hash (Unit* unit)
{
  return Hash::hash(reinterpret_cast<void*>(unit));
}
