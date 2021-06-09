/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Shuffling.cpp
 * Implementing the normalisation inference rule.
 * @since 25/12/2003 Manchester
 */

#include "Lib/Sort.hpp"
#include "Lib/Environment.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SubformulaIterator.hpp"
#include "Kernel/Unit.hpp"

#include "Shuffling.hpp"

using namespace Kernel;
using namespace Shell;

/**
 * Shuffle a problem
 */
void Shuffling::shuffle(Problem& prb)
{
  CALL("Shuffling::shuffle (Problem&)");

  shuffle(prb.units());
}

/**
 * Shuffle a list of units by shuffling every unit in it and
 * also shuffling the list itself.
 * @since 09/06/2021 Prague
 */
void Shuffling::shuffle (UnitList*& units)
{
  CALL("Shuffling::shuffle (UnitList*&)");

  shuffleList(units);

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    shuffle(us.next());
  }
} // Shuffling::shuffle (UnitList*)

void Shuffling::shuffle(Unit* unit)
{
  CALL("Shuffling::shuffle (Unit*");

  // cout << "Bef: " << unit->toString() << endl;

  if (unit->isClause()) {
    shuffle(unit->asClause());
  } else {
    shuffle(static_cast<FormulaUnit*>(unit)->formula());
  }

  //cout << "Aft: " << unit->toString() << endl;
}

void Shuffling::shuffle(Clause* clause)
{
  CALL("Shuffling::shuffle (Clause*)");

  shuffleArray(*clause,clause->length());

  clause->notifyLiteralReorder();
}

void Shuffling::shuffle(Formula* fla)
{
  CALL("Shuffling::shuffle (Formula*)");

}
