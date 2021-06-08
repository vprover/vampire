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
  CALL("Shuffling::shuffle");

  UnitList* units = prb.units();
  units = shuffle(units);
  prb.units() = units;
}

/**
 * Shuffle a list of units by shuffling every unit in it and
 * also shuffling the list itself.
 * @since 09/06/2021 Prague
 */
UnitList* Shuffling::shuffle (UnitList* units)
{
  CALL("Shuffling::shuffle (UnitList*");

  if (UnitList::isEmpty(units)) {
    return units;
  }

  unsigned length = UnitList::length(units);

  DArray<Unit*> aux(length);
  unsigned idx = 0;

  UnitList::Iterator us(units);
  while (us.hasNext()) {
    Unit* unit = us.next();
    aux[idx++] = shuffle(unit);
  }

  // this should be a library function somewhere:
  for(unsigned i=0;i<length;i++){
    unsigned j = Random::getInteger(length-i)+i;
    std::swap(aux[i],aux[j]);
  }

  UnitList* result = UnitList::empty();
  for (idx = 0; idx < length; idx++) {
    // cout << aux[idx]->toString() << endl;
    result = new UnitList(aux[idx],result);
  }
  UnitList::destroy(units);
  return result;
} // Shuffling::shuffle (UnitList*)

Unit* Shuffling::shuffle(Unit* unit)
{
  CALL("Shuffling::shuffle (Unit*");

  /*
  cout << "Bef: " << unit->toString() << endl;

  if (unit->isClause()) {
    Clause& clause = *static_cast<Clause*>(unit);
    int length = clause.length();

    for(unsigned i=0;i<length;i++){
      unsigned j = Random::getInteger(length-i)+i;
      std::swap(clause[i],clause[j]);

      // clause[i] is fixed now, let's potentially swap LHS and RHS
      if (!clause[i]->shared()) {
        // more shuffling here? (shared literals are internally normalized)
      }
    }

    // more than one literal
    Sort<Literal*,Normalisation> srt(length,*this);
    for (int i = 0;i < length;i++) {
      srt.add(clause[i]);
    }
    srt.sort();
    for (int i=0;i < length;i++) {
      clause[i] = srt[i];
    }

    clause.notifyLiteralReorder();
  } else {


  }

  cout << "Aft: " << unit->toString() << endl;
  */

  return unit;
}
