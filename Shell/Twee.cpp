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
 * Implements Twee's goal-directed preprocessing technique for equational reasoning.
 * To quote "Twee: An Equational Theorem Prover" (Smallbone, 2021):
 *
 * ----- 
 * Twee’s frontend can optionally transform the problem to make the prover more goal-directed.
 * The transformation is simple, but strange.
 * For every function term f(...) appearing in the goal, we introduce a fresh constant symbol a and add the axiom f(...) = a
 * For example, if the goal is f(g(a), b) = h(c) we add the axioms f(g(a), b) = sF0, g(a) = sF1, and h(c) = sF2.
 * Simplification will rewrite the first axiom to f(sF1, b) = sF0 and the goal to sF0 = sF2.
 * -----
 * 
 * We take an intepretation of this for our purposes, NB:
 *  - any ground term, in a clause derived from the conjecture, is transformed in this way
 *  - introduced definitions are considered derived from the conjecture
 */

#include "Kernel/Clause.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/TermIterators.hpp"

#include "Twee.hpp"

using Kernel::Clause;
using Kernel::Literal;
using Kernel::Problem;
using Kernel::Unit;
using Kernel::UnitList;

void Shell::Twee::apply(Problem &prb)
{
  CALL("Twee::apply");

  bool modified = false;

  UnitList::Iterator uit(prb.units());
  while (uit.hasNext()) {
    Unit *u = uit.next();
    if (!u->derivedFromGoal())
      continue;

    ASS(u->isClause());
    Clause *c = u->asClause();
    for (unsigned i = 0; i < c->size(); i++) {
      Literal *l = c->literals()[i];
      NonVariableNonTypeIterator subterms(l);
      while (subterms.hasNext()) {
        modified |= handleTerm(prb, subterms.next());
      }
    }
  }
  if (modified) {
    prb.reportFormulasAdded();
    prb.reportEqualityAdded(false);
  }
}

bool Shell::Twee::handleTerm(Problem &prb, TermList tl)
{
  CALL("Twee:::handleTerm");
  ASS(tl.isTerm());

  Term *t = tl.term();
  if (!t->ground() || t->arity() == 0 || !_seen.insert(t))
    return false;

  TermList sort = SortHelper::getResultSort(t);
  OperatorType *type = OperatorType::getConstantsType(sort);
  unsigned symbol = env.signature->addFreshFunction(0, "sF");
  env.signature->getFunction(symbol)->setType(type);
  TermList constant = TermList(Term::createConstant(symbol));
  Literal *equation = Literal::createEquality(true, tl, constant, sort);
  Inference inference(NonspecificInference0(
      UnitInputType::AXIOM,
      InferenceRule::DEFINITION_FOLDING));
  Clause *clause = new (1) Clause(1, inference);
  clause->literals()[0] = equation;

  if(env.options->showPreprocessing()) {
    env.out() << "[PP] twee: " << clause->toString() << std::endl;
  }

  prb.addUnits(new UnitList(clause));
  return true;
}
