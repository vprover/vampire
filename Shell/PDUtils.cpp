
/*
 * File PDUtils.cpp.
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
 * @file PDUtils.cpp
 * Implements class PDUtils.
 */

#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/MultiCounter.hpp"
#include "Lib/Stack.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Signature.hpp"

#include "PDUtils.hpp"

namespace Shell
{

/**
 * Return true if literal can act as a definition head (i.e. is not equality,
 * has only variable subterms, and these subterms are all distinct)
 */
bool PDUtils::isDefinitionHead(Literal* l)
{
  CALL("PDUtils::isDefinitionHead");

  Signature::Symbol* sym = env.signature->getPredicate(l->functor());
  if(sym->protectedSymbol()) {
    return false;
  }

  unsigned ar = l->arity();
  if(l->weight()!=ar+1 || l->getDistinctVars()!=ar) {
    return false;
  }
  return true;
}

/**
 * Return true if unit is an equivalence between atoms with
 * all variables quantified on the top level.
 */
bool PDUtils::isAtomEquivalence(FormulaUnit* unit, Literal*& lit1, Literal*& lit2)
{
  CALL("PDUtils::isAtomEquivalence(FormulaUnit*,Literal*&,Literal*&)");

  Formula* f1;
  Formula* f2;
  if(!isAtomEquivalence(unit, f1, f2)) {
    return false;
  }
  lit1 = f1->literal();
  lit2 = f2->literal();
  return true;
}

bool PDUtils::isUnitAtom(FormulaUnit* unit, Formula*& atom)
{
  CALL("PDUtils::isUnitAtom");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()!=LITERAL) {
    return false;
  }
  atom = f;
  return true;
}

/**
 * Return true if unit is an equivalence, implication or XOR between atoms with
 * all variables quantified at the top level.
 */
bool PDUtils::isAtomBinaryFormula(FormulaUnit* unit, Connective& con, Formula*& f1, Formula*& f2)
{
  CALL("PDUtils::isAtomBinaryFormula");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  Connective c = f->connective();
  if(c!=IFF && c!=IMP && c!=XOR) {
    return false;
  }
  if(f->left()->connective()!=LITERAL || f->right()->connective()!=LITERAL) {
    return false;
  }

  con = c;
  f1 = f->left();
  f2 = f->right();
  return true;
}

/**
 * Return true if unit is an equivalence between atoms with
 * all variables quantified at the top level.
 */
bool PDUtils::isAtomEquivalence(FormulaUnit* unit, Formula*& f1, Formula*& f2)
{
  CALL("PDUtils::isAtomEquivalence");

  Formula* auxF1;
  Formula* auxF2;
  Connective con;
  if(!isAtomBinaryFormula(unit, con, auxF1, auxF2) || con!=IFF) {
    return false;
  }
  f1 = auxF1;
  f2 = auxF2;
  return true;
}

bool PDUtils::isPredicateEquivalence(FormulaUnit* unit)
{
  CALL("PDInliner::isPredicateEquivalence/1");

  Formula* aux1;
  Formula* aux2;
  return isPredicateEquivalence(unit, aux1, aux2);
}

bool PDUtils::isPredicateEquivalence(FormulaUnit* unit, unsigned& pred1, unsigned& pred2)
{
  CALL("PDInliner::isPredicateEquivalence(FormulaUnit*,unsigned&,unsigned&)");

  Literal* l1;
  Literal* l2;
  if(isPredicateEquivalence(unit, l1, l2)) {
    pred1 = l1->functor();
    pred2 = l2->functor();
    return true;
  }
  return false;
}

bool PDUtils::isPredicateEquivalence(FormulaUnit* unit, Literal*& lit1, Literal*& lit2)
{
  CALL("PDInliner::isPredicateEquivalence(FormulaUnit*,Literal*&,Literal*&)");

  Formula* f1;
  Formula* f2;
  if(!isPredicateEquivalence(unit, f1, f2)) {
    return false;
  }
  lit1 = f1->literal();
  lit2 = f2->literal();
  return true;
}

/**
 * If unit is predicate equivalence, return true and
 * into f1 and f2 assign the equivalent atomic formulas.
 */
bool PDUtils::isPredicateEquivalence(FormulaUnit* unit, Formula*& f1, Formula*& f2)
{
  CALL("PDInliner::isPredicateEquivalence(FormulaUnit*,Formula*&,Formula*&)");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()!=IFF) {
    return false;
  }
  if(f->left()->connective()!=LITERAL || f->right()->connective()!=LITERAL) {
    return false;
  }
  Literal* l1 = f->left()->literal();
  Literal* l2 = f->right()->literal();

  if(l1->arity()!=l2->arity() || !isDefinitionHead(l1) || !isDefinitionHead(l2)) {
    return false;
  }
  if(!l1->containsAllVariablesOf(l2)) {
    return false;
  }
  if(l1->functor()==l2->functor()) {
    return false;
  }
  f1 = f->left();
  f2 = f->right();
  return true;
}


/**
 * Split a definition which isn't an equivalence between predicates into
 * lhs and rhs.
 *
 * We don't allow equivalences between predicates in order to make the
 * split deterministic.
 */
void PDUtils::splitDefinition(FormulaUnit* unit, Literal*& lhs, Formula*& rhs)
{
  CALL("PDUtils::splitDefinition");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()==LITERAL) {
    ASS(isDefinitionHead(f->literal()));
    lhs = f->literal();
    rhs = Formula::trueFormula();
    return;
  }
  ASS_EQ(f->connective(),IFF);

  if(f->left()->connective()==LITERAL) {
    if(hasDefinitionShape(f->left()->literal(), f->right())) {
      //we don't allow predicate equivalences here
      ASS(f->right()->connective()!=LITERAL || !hasDefinitionShape(f->right()->literal(), f->left()));
      lhs = f->left()->literal();
      rhs = f->right();
      return;
    }
  }
  ASS_EQ(f->right()->connective(),LITERAL);
  ASS(hasDefinitionShape(f->right()->literal(), f->left()));
  lhs = f->right()->literal();
  rhs = f->left();
}

/**
 * Perform local checks whether givan formula can be a definition.
 *
 * True is returned also for predicate equivalences.
 */
bool PDUtils::hasDefinitionShape(FormulaUnit* unit)
{
  CALL("PDUtils::hasDefinitionShape/1");

  Formula* f = unit->formula();
  if(f->connective()==FORALL) {
    f = f->qarg();
  }
  if(f->connective()==LITERAL) {
    if(isDefinitionHead(f->literal())) {
      return true;
    }
  }
  if(f->connective()!=IFF) {
    return false;
  }
  if(f->left()->connective()==LITERAL) {
    if(hasDefinitionShape(f->left()->literal(), f->right())) {
      return true;
    }
  }
  if(f->right()->connective()==LITERAL) {
    return hasDefinitionShape(f->right()->literal(), f->left());
  }
  return false;
}

/**
 * Perform local checks whether givan formula can be a definition.
 *
 * Check whether lhs is not an equality and its arguments are distinct
 * variables. Also check that there are no unbound variables in the body
 * that wouldn't occur in the lhs, and that the lhs predicate doesn't occur
 * in the body.
 */
bool PDUtils::hasDefinitionShape(Unit* unit)
{
  if(unit->isClause()) { return false; }
  return hasDefinitionShape(static_cast<FormulaUnit*>(unit));
}

/**
 * Perform local checks whether givan formula can be a definition.
 *
 * Check whether lhs is not protected and its arguments are distinct
 * variables. Also check that there are no unbound variables in the body
 * that wouldn't occur in the lhs, and that the lhs predicate doesn't occur
 * in the body.
 */
bool PDUtils::hasDefinitionShape(Literal* lhs, Formula* rhs)
{
  CALL("PDUtils::hasDefinitionShape/2");

  if(!isDefinitionHead(lhs)) {
    return false;
  }

  unsigned defPred = lhs->functor();

  MultiCounter counter;
  for (const TermList* ts = lhs->args(); ts->isNonEmpty(); ts=ts->next()) {
    ASS(ts->isVar()); // follows from isDefinitionHead(lhs)==true
    int w = ts->var();
    ASS_EQ(counter.get(w),0); // that each var occurs only once follows from isDefinitionHead(lhs)==true
    counter.inc(w);
  }

  static Stack<unsigned> bodyPredicates;
  bodyPredicates.reset();

  rhs->collectPredicates(bodyPredicates);
  if(bodyPredicates.find(defPred)) {
    return false;
  }

  {
    Formula::VarList* freeVars = rhs->freeVariables();
    bool extraFreeVars = false;
    while(freeVars) {
      unsigned v = Formula::VarList::pop(freeVars);
      if(!counter.get(v)) {
	extraFreeVars = true;
      }
    }
    if(extraFreeVars) {
      return false;
    }
  }

  return true;
}

}
