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


bool PDUtils::isPredicateEquivalence(FormulaUnit* unit)
{
  CALL("PDInliner::isPredicateEquivalence/1");

  unsigned aux1, aux2;
  return isPredicateEquivalence(unit, aux1, aux2);
}

bool PDUtils::isPredicateEquivalence(FormulaUnit* unit, unsigned& pred1, unsigned& pred2)
{
  CALL("PDInliner::isPredicateEquivalence/3");

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
  pred1 = l1->functor();
  pred2 = l2->functor();
  return pred1!=pred2;
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
  ASS_EQ(f->connective(),IFF);

  if(f->left()->connective()==LITERAL) {
    if(hasDefinitionShape(unit, f->left()->literal(), f->right())) {
      //we don't allow predicate equivalences here
      ASS(f->right()->connective()!=LITERAL || !hasDefinitionShape(unit, f->right()->literal(), f->left()));
      lhs = f->left()->literal();
      rhs = f->right();
      return;
    }
  }
  ASS_EQ(f->right()->connective(),LITERAL);
  ASS(hasDefinitionShape(unit, f->right()->literal(), f->left()));
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
  if(f->connective()!=IFF) {
    return false;
  }
  if(f->left()->connective()==LITERAL) {
    if(hasDefinitionShape(unit, f->left()->literal(), f->right())) {
      return true;
    }
  }
  if(f->right()->connective()==LITERAL) {
    return hasDefinitionShape(unit, f->right()->literal(), f->left());
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
 * Check whether lhs is not an equality and its arguments are distinct
 * variables. Also check that there are no unbound variables in the body
 * that wouldn't occur in the lhs, and that the lhs predicate doesn't occur
 * in the body.
 */
bool PDUtils::hasDefinitionShape(FormulaUnit* unit, Literal* lhs, Formula* rhs)
{
  CALL("PDUtils::hasDefinitionShape/3");

  if(!isDefinitionHead(lhs)) {
    return false;
  }

  unsigned defPred = lhs->functor();

  MultiCounter counter;
  for (const TermList* ts = lhs->args(); ts->isNonEmpty(); ts=ts->next()) {
    if (! ts->isVar()) {
      return false;
    }
    int w = ts->var();
    if (counter.get(w) != 0) { // more than one occurrence
      return false;
    }
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
