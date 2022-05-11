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
 * @file Interpolants.cpp
 * Implements class Interpolants.
 */

#include "Kernel/InferenceStore.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"

#include "Interpolants.hpp"

namespace Shell
{

/**
 * Any pre-processing of the refutation before interpolation is considered.
 *
 * We remove the leafs corresponding to the conjecture
 * and leave the negated_conjecture child of this unit as the leaf instead.
 * (Inference::NEGATED_CONJECTURE is not sound).
 */
void Interpolants::removeConjectureNodesFromRefutation(Unit* refutation)
{
  CALL("Interpolants::removeConjectureNodesFromRefutation");

  Stack<Unit*> todo;
  DHSet<Unit*> seen;

  todo.push(refutation);
  while (todo.isNonEmpty()) {
    Unit* cur = todo.pop();
    if (!seen.insert(cur)) {
      continue;
    }

    if (cur->inference().rule() == InferenceRule::NEGATED_CONJECTURE) {
      VirtualIterator<Unit*> pars = InferenceStore::instance()->getParents(cur);

      // negating the conjecture is not a sound inference,
      // we want to consider the proof only from the point where it has been done already

      ASS(pars.hasNext()); // negating a conjecture should have exactly one parent
      Unit* par = pars.next();

      // so we steal parent's inherited color
      cur->setInheritedColor(par->inheritedColor());

      // and pretend there is no parent

      ASS(!pars.hasNext()); // negating a conjecture should have exactly one parent

      cur->inference().destroy();
      cur->inference() = Inference(NonspecificInference0(UnitInputType::NEGATED_CONJECTURE,InferenceRule::NEGATED_CONJECTURE)); // negated conjecture without a parent (non-standard, but nobody will see it)
    }

    todo.loadFromIterator(InferenceStore::instance()->getParents(cur));
  }
}

/**
 * Turn all Units in a refutation into FormulaUnits (casting Clauses to Formulas and wrapping these as Units).
 *
 * Keep the old refutation (= non-destructive). Possible sharing of the formula part of the original refutation.
 *
 * Assume that once we have formula on a parent path we can't go back to a clause.
 *
 */
Unit* Interpolants::formulifyRefutation(Unit* refutation)
{
  CALL("Interpolants::formulifyRefutation");

  Stack<Unit*> todo;
  DHMap<Unit*,Unit*> translate; // for caching results (we deal with a DAG in general), but also to distinguish the first call from the next

  todo.push(refutation);
  while (todo.isNonEmpty()) {
    Unit* cur = todo.top();

    if (translate.find(cur)) {  // the DAG hit case
      todo.pop();

      continue;
    }

    if (!cur->isClause()) {     // the formula case
      todo.pop();

      translate.insert(cur,cur);
      continue;
    }

    // are all children done?
    bool allDone = true;
    Inference& inf = cur->inference();
    Inference::Iterator iit = inf.iterator();
    while (inf.hasNext(iit)) {
      Unit* premUnit=inf.next(iit);
      if (!translate.find(premUnit)) {
        allDone = false;
        break;
      }
    }

    if (allDone) { // ready to return
      todo.pop();

      List<Unit*>* prems = 0;

      Inference::Iterator iit = inf.iterator();
      while (inf.hasNext(iit)) {
        Unit* premUnit=inf.next(iit);

        List<Unit*>::push(translate.get(premUnit), prems);
      }

      InferenceRule rule=inf.rule();
      prems = List<Unit*>::reverse(prems);  //we want items in the same order

      Formula* f = Formula::fromClause(cur->asClause());
      FormulaUnit* fu = new FormulaUnit(f,NonspecificInferenceMany(rule,prems));

      if (cur->inheritedColor() != COLOR_INVALID) {
        fu->setInheritedColor(cur->inheritedColor());
      }

      translate.insert(cur,fu);
    } else { // need "recursive" calls first

      Inference::Iterator iit = inf.iterator();
      while (inf.hasNext(iit)) {
        Unit* premUnit=inf.next(iit);
        todo.push(premUnit);
      }
    }
  }

  return translate.get(refutation);
}

}