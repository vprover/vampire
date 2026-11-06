#include "Lemma1.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/SortHelper.hpp"

#include "Lib/DHSet.hpp"
#include "Lib/List.hpp"

#include "Shell/EqualityProxy.hpp"
#include "Shell/EqualityProxyMono.hpp"
#include "Shell/Options.hpp"

#include "Lib/Environment.hpp"
#include "F02Fragment/FO2Logger.hpp"

#include <iostream>
#include <string>

using namespace Kernel;
using namespace Shell;

namespace FO2Fragment {
namespace {

unsigned getPredForConstant(unsigned constantFunctor, DHMap<unsigned, unsigned> &constants)
{
  unsigned predicateFunctor;
  if (!constants.find(constantFunctor, predicateFunctor)) {
    std::string constName = env.signature->getFunction(constantFunctor)->name();
    std::string predName = "p_" + constName;
    predicateFunctor = env.signature->addFreshPredicate(1, predName.c_str());
    constants.insert(constantFunctor, predicateFunctor);
  }
  return predicateFunctor;
}

bool isConstantTerm(TermList tl)
{
  return !tl.isVar() && tl.term()->arity() == 0;
}

/**
 * Implements Table 1 of Lemma 1 (de Nivelle & Pratt-Hartmann, Page 215)
 */
Formula *replaceinAtomicFormula(Formula *formula, DHMap<unsigned, unsigned> &constants)
{
  if (!formula) return nullptr;
  ASS_EQ(formula->connective(), LITERAL);

  Literal *lit = formula->literal();
  if (!lit) return formula;

  const TermList sort = AtomicSort::defaultSort();

  // Equality literal
  if (lit->isEquality()) {
    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    bool isConst0 = isConstantTerm(arg0);
    bool isConst1 = isConstantTerm(arg1);

    if (!isConst0 && !isConst1) return formula;

    if (isConst0 && !isConst1) {
      unsigned pred0 = getPredForConstant(arg0.term()->functor(), constants);
      unsigned otherVar = arg1.isVar() ? arg1.var() : 0;
      unsigned freshVar = (otherVar == 0) ? 1 : 0;

      Literal *eqLit = Literal::createEquality(lit->polarity(), TermList::var(freshVar), arg1, sort);
      Literal *pLit = Literal::create1(pred0, true, TermList::var(freshVar));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit), andArgs);
      FormulaList::push(new AtomicFormula(eqLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      return new QuantifiedFormula(EXISTS, VSList::singleton({freshVar, sort}), conj);
    }
    else if (!isConst0 && isConst1) {
      unsigned pred1 = getPredForConstant(arg1.term()->functor(), constants);
      unsigned otherVar = arg0.isVar() ? arg0.var() : 0;
      unsigned freshVar = (otherVar == 0) ? 1 : 0;

      Literal *eqLit = Literal::createEquality(lit->polarity(), arg0, TermList::var(freshVar), sort);
      Literal *pLit = Literal::create1(pred1, true, TermList::var(freshVar));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit), andArgs);
      FormulaList::push(new AtomicFormula(eqLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      return new QuantifiedFormula(EXISTS, VSList::singleton({freshVar, sort}), conj);
    }
    else { // Both are constants
      unsigned pred0 = getPredForConstant(arg0.term()->functor(), constants);
      unsigned pred1 = getPredForConstant(arg1.term()->functor(), constants);

      Literal *eqLit = Literal::createEquality(lit->polarity(), TermList::var(0), TermList::var(1), sort);
      Literal *pLit0 = Literal::create1(pred0, true, TermList::var(0));
      Literal *pLit1 = Literal::create1(pred1, true, TermList::var(1));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit1), andArgs);
      FormulaList::push(new AtomicFormula(pLit0), andArgs);
      FormulaList::push(new AtomicFormula(eqLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      Formula *exists1 = new QuantifiedFormula(EXISTS, VSList::singleton({1u, sort}), conj);
      return new QuantifiedFormula(EXISTS, VSList::singleton({0u, sort}), exists1);
    }
  }

  // Non-equality literal
  unsigned arity = lit->arity();
  if (arity == 0) return formula;

  bool hasConstant = false;
  for (unsigned i = 0; i < arity; ++i) {
    if (isConstantTerm(*lit->nthArgument(i))) {
      hasConstant = true;
      break;
    }
  }

  if (!hasConstant) return formula;

  if (arity == 1) {
    TermList arg0 = *lit->nthArgument(0);
    if (isConstantTerm(arg0)) {
      unsigned pred0 = getPredForConstant(arg0.term()->functor(), constants);
      unsigned freshVar = 0;

      Literal *modLit = Literal::create1(lit->functor(), lit->polarity(), TermList::var(freshVar));
      Literal *pLit = Literal::create1(pred0, true, TermList::var(freshVar));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit), andArgs);
      FormulaList::push(new AtomicFormula(modLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      return new QuantifiedFormula(EXISTS, VSList::singleton({freshVar, sort}), conj);
    }
  }
  else if (arity == 2) {
    TermList arg0 = *lit->nthArgument(0);
    TermList arg1 = *lit->nthArgument(1);

    bool isConst0 = isConstantTerm(arg0);
    bool isConst1 = isConstantTerm(arg1);

    if (isConst0 && !isConst1) {
      unsigned pred0 = getPredForConstant(arg0.term()->functor(), constants);
      unsigned otherVar = arg1.isVar() ? arg1.var() : 0;
      unsigned freshVar = (otherVar == 0) ? 1 : 0;

      TermList newArgs[2] = {TermList::var(freshVar), arg1};
      Literal *modLit = Literal::create(lit->functor(), 2, lit->polarity(), newArgs);
      Literal *pLit = Literal::create1(pred0, true, TermList::var(freshVar));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit), andArgs);
      FormulaList::push(new AtomicFormula(modLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      return new QuantifiedFormula(EXISTS, VSList::singleton({freshVar, sort}), conj);
    }
    else if (!isConst0 && isConst1) {
      unsigned pred1 = getPredForConstant(arg1.term()->functor(), constants);
      unsigned otherVar = arg0.isVar() ? arg0.var() : 0;
      unsigned freshVar = (otherVar == 0) ? 1 : 0;

      TermList newArgs[2] = {arg0, TermList::var(freshVar)};
      Literal *modLit = Literal::create(lit->functor(), 2, lit->polarity(), newArgs);
      Literal *pLit = Literal::create1(pred1, true, TermList::var(freshVar));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit), andArgs);
      FormulaList::push(new AtomicFormula(modLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      return new QuantifiedFormula(EXISTS, VSList::singleton({freshVar, sort}), conj);
    }
    else if (isConst0 && isConst1) {
      unsigned pred0 = getPredForConstant(arg0.term()->functor(), constants);
      unsigned pred1 = getPredForConstant(arg1.term()->functor(), constants);

      TermList newArgs[2] = {TermList::var(0), TermList::var(1)};
      Literal *modLit = Literal::create(lit->functor(), 2, lit->polarity(), newArgs);
      Literal *pLit0 = Literal::create1(pred0, true, TermList::var(0));
      Literal *pLit1 = Literal::create1(pred1, true, TermList::var(1));

      FormulaList *andArgs = FormulaList::empty();
      FormulaList::push(new AtomicFormula(pLit1), andArgs);
      FormulaList::push(new AtomicFormula(pLit0), andArgs);
      FormulaList::push(new AtomicFormula(modLit), andArgs);
      Formula *conj = JunctionFormula::generalJunction(AND, andArgs);

      Formula *exists1 = new QuantifiedFormula(EXISTS, VSList::singleton({1u, sort}), conj);
      return new QuantifiedFormula(EXISTS, VSList::singleton({0u, sort}), exists1);
    }
  }

  return formula;
}

Formula *makeUniquenessAxiom(unsigned predicateFunctor)
{
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("\n--- GENERAZIONE ASSIOMA DI UNICITA' ---");
  }

  const TermList sort = AtomicSort::defaultSort();
  TermList x = TermList::var(0);
  TermList y = TermList::var(1);

  Formula *predY = new AtomicFormula(Literal::create1(predicateFunctor, true, y));
  Formula *eq = new AtomicFormula(Literal::createEquality(true, x, y, sort));

  Formula *implication = new BinaryFormula(Connective::IMP, predY, eq);
  Formula *universalY = new QuantifiedFormula(Connective::FORALL,
                                              VSList::singleton({1u, sort}),
                                              implication);

  Formula *predX = new AtomicFormula(Literal::create1(predicateFunctor, true, x));

  FormulaList *andArgs = FormulaList::empty();
  FormulaList::push(universalY, andArgs);
  FormulaList::push(predX, andArgs);
  Formula *conjunction = JunctionFormula::generalJunction(Connective::AND, andArgs);

  Formula *finalAxiom = new QuantifiedFormula(Connective::EXISTS,
                                              VSList::singleton({0u, sort}),
                                              conjunction);

  return finalAxiom;
}

Formula *replaceInFormula(Formula *formula, DHMap<unsigned, unsigned> &constants)
{
  if (!formula) return nullptr;

  switch (formula->connective()) {
    case LITERAL:
      return replaceinAtomicFormula(formula, constants);

    case IMP:
    case IFF:
    case XOR: {
      Formula *newLeft = replaceInFormula(formula->left(), constants);
      Formula *newRight = replaceInFormula(formula->right(), constants);
      if (newLeft != formula->left() || newRight != formula->right()) {
        return new BinaryFormula(formula->connective(), newLeft, newRight);
      }
      return formula;
    }
    case AND:
    case OR: {
      FormulaList *args = formula->args();
      FormulaList *newArgs = FormulaList::empty();
      bool changed = false;

      FormulaList::Iterator it(args);
      while (it.hasNext()) {
        Formula *arg = it.next();
        Formula *newArg = replaceInFormula(arg, constants);
        if (newArg != arg) changed = true;
        FormulaList::push(newArg, newArgs);
      }
      newArgs = FormulaList::reverse(newArgs);

      if (changed) {
        return new JunctionFormula(formula->connective(), newArgs);
      }
      FormulaList::destroy(newArgs);
      return formula;
    }
    case NOT: {
      Formula *newArg = replaceInFormula(formula->uarg(), constants);
      if (newArg != formula->uarg()) {
        return new NegatedFormula(newArg);
      }
      return formula;
    }
    case FORALL:
    case EXISTS: {
      Formula *newSub = replaceInFormula(formula->qarg(), constants);
      if (newSub != formula->qarg()) {
        return new QuantifiedFormula(formula->connective(), formula->vars(), newSub);
      }
      return formula;
    }
    default:
      return formula;
  }
}

Unit *replaceInClause(Clause *cl, DHMap<unsigned, unsigned> &constants)
{
  bool modified = false;
  Stack<Formula *> processedLiterals;

  const unsigned len = cl->length();
  for (unsigned i = 0; i < len; ++i) {
    Literal *lit = (*cl)[i];
    Formula *litFormula = new AtomicFormula(lit);
    Formula *processedFormula = replaceInFormula(litFormula, constants);

    if (processedFormula != litFormula) {
      modified = true;
    }
    processedLiterals.push(processedFormula);
  }

  if (!modified) {
    return cl;
  }

  FormulaList *disjuncts = FormulaList::empty();
  while (!processedLiterals.isEmpty()) {
    FormulaList::push(processedLiterals.pop(), disjuncts);
  }

  Formula *fullDisjunction = JunctionFormula::generalJunction(OR, disjuncts);

  return new FormulaUnit(fullDisjunction,
                         NonspecificInference1(InferenceRule::INPUT, cl));
}

} // namespace

void Lemma1::applyLemma1(Kernel::Problem &prb)
{
  DHMap<unsigned, unsigned> constants;

  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    Unit *unit = it.next();

    if (!unit->isClause()) {
      FormulaUnit *fu = static_cast<FormulaUnit *>(unit);
      Formula *originFormula = fu->formula();

      Formula *processedFormula = replaceInFormula(originFormula, constants);

      if (processedFormula != originFormula) {
        FormulaUnit *newUnit = new FormulaUnit(processedFormula, NonspecificInference1(InferenceRule::INPUT, unit));
        it.replace(newUnit);
      }
    }
    else {
      Clause *cl = static_cast<Clause *>(unit);
      Unit *processedUnit = replaceInClause(cl, constants);

      if (processedUnit != cl) {
        it.replace(processedUnit);
      }
    }
  }

  if (!constants.isEmpty()) {
    UnitList *newUnits = UnitList::empty();

    DHMap<unsigned, unsigned>::Iterator mit(constants);
    while (mit.hasNext()) {
      unsigned constantSymbolId;
      unsigned predicateSymbolId;
      mit.next(constantSymbolId, predicateSymbolId);

      Formula *uniquenessFormula = makeUniquenessAxiom(predicateSymbolId);
      Unit *uniquenessUnit = new FormulaUnit(uniquenessFormula, Inference(FromInput(UnitInputType::AXIOM)));
      UnitList::push(uniquenessUnit, newUnits);
    }
    prb.units() = UnitList::concat(newUnits, prb.units());
  }
}
} // namespace FO2Fragment