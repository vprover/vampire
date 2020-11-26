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
 * @file ColorHelper.cpp
 * Implements class ColorHelper.
 */

#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "Clause.hpp"
#include "EqHelper.hpp"
#include "Inference.hpp"
#include "Renaming.hpp"
#include "Signature.hpp"
#include "Term.hpp"
#include "TermIterators.hpp"

#include "ColorHelper.hpp"

namespace Kernel
{

/**
 * Return true if symbol number @c functor is transparent. If @c predicate
 * is true, we assume @c functor to be predicate number, otherwise it is
 * a function number.
 */
bool ColorHelper::isTransparent(bool predicate, unsigned functor)
{
  CALL("ColorHelper::isTransparent");

  Signature::Symbol* sym;
  if (predicate) {
    sym = env.signature->getPredicate(functor);
  }
  else {
    sym = env.signature->getFunction(functor);
  }
  return sym->color()==COLOR_TRANSPARENT;
}

bool ColorHelper::hasColoredPredicates(Clause* c)
{
  CALL("ColorHelper::hasColoredPredicates");

  unsigned clen = c->length();
  for (unsigned i=0; i<clen; i++) {
    Literal* lit = (*c)[i];

    if (!isTransparent(true, lit->functor())) {
      return true;
    }
  }
  return false;
}

/**
 * collect all occurrences colored constants of a clause c in the stack acc
 * @since 04/05/2013 Manchester, improved to use new NonVariableIterator
 * @author Andrei Voronkov
 */
void ColorHelper::collectColoredConstants(Clause* c, Stack<Term*>& acc)
{
  CALL("ColorHelper::collectColoredConstants");

  unsigned clen = c->length();
  for (unsigned i=0; i<clen; i++) {
    Literal* lit = (*c)[i];

    NonVariableIterator tit(lit,true);
    while (tit.hasNext()) {
      Term* t = tit.next().term();
      if (t->color() == COLOR_TRANSPARENT) {
	tit.right();
	continue;
      }
      if (t->arity() == 0) {
	acc.push(t);
      }
    }
  }
} // collectColoredConstants

Clause* ColorHelper::skolemizeColoredConstants(Clause* c)
{
  CALL("ColorHelper::skolemizeColoredConstants");

  Stack<Term*> coloredConstants;
  collectColoredConstants(c,coloredConstants);
  if (coloredConstants.isEmpty()) {
    return 0;
  }

  unsigned clen = c->length();
  static LiteralStack resStack;
  resStack.reset();
  resStack.loadFromIterator(Clause::Iterator(*c));

  ASS_EQ(resStack.size(), clen);

  while (coloredConstants.isNonEmpty()) {
    TermList replaced = TermList(coloredConstants.pop());

    unsigned newFn = env.signature->addSkolemFunction(0);
    TermList newTrm = TermList(Term::create(newFn, 0, 0));

    for (unsigned i=0; i<clen; i++) {
      resStack[i] = EqHelper::replace(resStack[i], replaced, newTrm);
    }
  }
  Clause* res = Clause::fromStack(resStack, NonspecificInference1(InferenceRule::COLOR_UNBLOCKING, c));
  return res;
}

void ColorHelper::ensureSkolemReplacement(Term* t, TermMap& map)
{
  CALL("ColorHelper::ensureSkolemReplacement");

  //TODO: check also for generalization, or even better, first
  //find the most general colored terms, and make skolem replacements
  //only for those

  Term* norm = Renaming::normalize(t);
  if (map.find(norm)) {
    return;
  }
  unsigned varCnt = norm->getDistinctVars();
  unsigned newFn = env.signature->addSkolemFunction(varCnt, "CU");

  static Stack<TermList> argStack;
  argStack.reset();
  //variables in normalized term are X0,..X<varCnt-1>, so we put the
  //same into the Skolem term
  for (unsigned i=0; i<varCnt; i++) {
    argStack.push(TermList(i, false));
  }
  Term* replacement = Term::create(newFn, varCnt, argStack.begin());
  map.insert(norm, replacement);
}

void ColorHelper::collectSkolemReplacements(Clause* c, TermMap& map)
{
  CALL("ColorHelper::collectSkolemReplacements");

  unsigned clen = c->length();
  for (unsigned i=0; i<clen; i++) {
    Literal* lit = (*c)[i];

    NonVariableIterator tit(lit,true);
    while (tit.hasNext()) {
      Term* t = tit.next().term();
      if (!isTransparent(false, t->functor())) {
	ensureSkolemReplacement(t, map);
	//we will replace this term, so we do not descend into it
	tit.right();
      }
    }
  }
}

Term* ColorHelper::applyReplacement(Term* t, TermMap& map)
{
  CALL("ColorHelper::applyReplacement");

  Renaming r;
  r.normalizeVariables(t);
  Term* norm = r.apply(t);
  ASS(map.find(norm));
  Term* tgtNorm = map.get(norm);

  Renaming inv;
  inv.makeInverse(r);
  Term* tgt = inv.apply(tgtNorm);
  ASS(tgt->containsAllVariablesOf(t));
  ASS(t->containsAllVariablesOf(tgt));
  ASS_EQ(tgt->color(), COLOR_TRANSPARENT);
  return tgt;
}

Clause* ColorHelper::skolemizeColoredTerms(Clause* c)
{
  CALL("ColorHelper::skolemizeColoredTerms");

  static TermMap replMap;
  replMap.reset();

  collectSkolemReplacements(c, replMap);
  if (replMap.isEmpty()) {
    return 0;
  }

  static LiteralStack resStack;
  resStack.reset();

  unsigned clen = c->length();
  for (unsigned i=0; i<clen; i++) {
    Literal* lit = (*c)[i];
  start_replacing:
    NonVariableIterator nvit(lit);
    while (nvit.hasNext()) {
      Term* t = nvit.next().term();
      if (!isTransparent(false,t->functor())) {
	//here we each time remove at least one colored symbol
	Term* newTrm = applyReplacement(t,replMap);
	lit = EqHelper::replace(lit,TermList(t),TermList(newTrm));
	goto start_replacing;
      }
    }
    resStack.push(lit);
  }

  ASS_EQ(resStack.size(), clen);
  Clause* res = Clause::fromStack(resStack, NonspecificInference1(InferenceRule::COLOR_UNBLOCKING, c));
  return res;
}

void ColorHelper::tryUnblock(Clause* c, SaturationAlgorithm* salg)
{
  CALL("ColorHelper::tryUnblock");

//  if (hasOnlyColoredConstants(c)) {
  if (!hasColoredPredicates(c)) {
//    Clause* unblocked = skolemizeColoredConstants(c);
    Clause* unblocked = skolemizeColoredTerms(c);
    if (unblocked) {
      if (env.options->showBlocked()) {
	env.beginOutput();
	env.out()<<"Unblocking clause "<<unblocked->toString()<<endl;
	env.endOutput();
      }
      salg->addNewClause(unblocked);
    }
  }

}

} // namespace Kernel
