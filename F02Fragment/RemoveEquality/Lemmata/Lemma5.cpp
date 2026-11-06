#include "Lemma5.hpp"
#include "F02Fragment/ScottTypes.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/SortHelper.hpp"
#include "Shell/Rectify.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Stack.hpp"
#include "F02Fragment/FO2Logger.hpp"

#include <iostream>
#include <vector>
#include <string>

using namespace Kernel;

namespace FO2Fragment {
namespace Lemmata {
namespace {

Kernel::Formula *replaceNegativeEquality(Kernel::Formula *formula, unsigned neqPredicate)
{
  if (!formula) return nullptr;

  switch (formula->connective()) {
    case Kernel::LITERAL: {
      Kernel::Literal *lit = formula->literal();
      if (!lit->isEquality() || lit->isPositive()) return formula;
      return new Kernel::AtomicFormula(Kernel::Literal::create2(
          neqPredicate, true, *lit->nthArgument(0), *lit->nthArgument(1)));
    }
    case Kernel::NOT: {
      Kernel::Formula *arg = formula->uarg();
      if (arg && arg->connective() == Kernel::LITERAL && arg->literal()->isEquality()) {
        if (arg->literal()->isPositive()) {
          return new Kernel::AtomicFormula(Kernel::Literal::create2(
              neqPredicate, true, *arg->literal()->nthArgument(0), *arg->literal()->nthArgument(1)));
        }
        // NOT of a negative equality is a positive equality, which is retained.
        return new Kernel::AtomicFormula(Kernel::Literal::create(arg->literal(), true));
      }
      Kernel::Formula *newArg = replaceNegativeEquality(arg, neqPredicate);
      return newArg == arg ? formula : new Kernel::NegatedFormula(newArg);
    }
    case Kernel::AND:
    case Kernel::OR: {
      Kernel::FormulaList *newArgs = Kernel::FormulaList::empty();
      bool changed = false;
      Kernel::FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {
        Kernel::Formula *oldArg = it.next();
        Kernel::Formula *newArg = replaceNegativeEquality(oldArg, neqPredicate);
        changed = changed || newArg != oldArg;
        Kernel::FormulaList::push(newArg, newArgs);
      }
      newArgs = Kernel::FormulaList::reverse(newArgs);
      if (!changed) {
        Kernel::FormulaList::destroy(newArgs);
        return formula;
      }
      return Kernel::JunctionFormula::generalJunction(formula->connective(), newArgs);
    }
    case Kernel::IMP:
    case Kernel::IFF:
    case Kernel::XOR: {
      Kernel::Formula *left = replaceNegativeEquality(formula->left(), neqPredicate);
      Kernel::Formula *right = replaceNegativeEquality(formula->right(), neqPredicate);
      if (left == formula->left() && right == formula->right()) return formula;
      return new Kernel::BinaryFormula(formula->connective(), left, right);
    }
    case Kernel::FORALL:
    case Kernel::EXISTS: {
      Kernel::Formula *arg = replaceNegativeEquality(formula->qarg(), neqPredicate);
      return arg == formula->qarg() ? formula
          : new Kernel::QuantifiedFormula(formula->connective(), formula->vars(), arg);
    }
    default:
      return formula;
  }
}

void eliminateNegativeEqualities(Kernel::Problem &prb)
{
  bool hasDisequality = false;
  Kernel::UnitList::Iterator scan(prb.units());
  while (scan.hasNext()) {
    Kernel::Unit *unit = scan.next();
    if (unit->isClause()) {
      Kernel::Clause *clause = static_cast<Kernel::Clause *>(unit);
      for (unsigned i = 0; i < clause->length(); ++i) {
        Kernel::Literal *lit = (*clause)[i];
        hasDisequality = hasDisequality || (lit->isEquality() && !lit->isPositive());
      }
    } else {
      Kernel::Formula *formula = static_cast<Kernel::FormulaUnit *>(unit)->formula();
      // Negative equality in NNF is represented by a negative-polarity literal.
      // Also recognize an explicit NOT applied to a positive equality literal.
      std::vector<Kernel::Formula *> pending{formula};
      while (!pending.empty()) {
        Kernel::Formula *current = pending.back();
        pending.pop_back();
        if (!current) continue;
        if (current->connective() == Kernel::LITERAL) {
          Kernel::Literal *lit = current->literal();
          hasDisequality = hasDisequality || (lit->isEquality() && !lit->isPositive());
        } else if (current->connective() == Kernel::NOT) {
          Kernel::Formula *arg = current->uarg();
          if (arg && arg->connective() == Kernel::LITERAL && arg->literal()->isEquality() &&
              arg->literal()->isPositive()) {
            hasDisequality = true;
          } else {
            pending.push_back(arg);
          }
        } else if (current->connective() == Kernel::AND || current->connective() == Kernel::OR) {
          Kernel::FormulaList::Iterator it(current->args());
          while (it.hasNext()) pending.push_back(it.next());
        } else if (current->connective() == Kernel::IMP || current->connective() == Kernel::IFF ||
                   current->connective() == Kernel::XOR) {
          pending.push_back(current->left());
          pending.push_back(current->right());
        } else if (current->connective() == Kernel::FORALL || current->connective() == Kernel::EXISTS) {
          pending.push_back(current->qarg());
        }
      }
    }
  }
  if (!hasDisequality) return;

  unsigned neqPredicate = env.signature->addFreshPredicate(2, "neq");
  Kernel::UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    Kernel::Unit *unit = it.next();
    if (unit->isClause()) {
      Kernel::Clause *clause = static_cast<Kernel::Clause *>(unit);
      Lib::Stack<Kernel::Literal *> literals;
      bool changed = false;
      for (unsigned i = 0; i < clause->length(); ++i) {
        Kernel::Literal *lit = (*clause)[i];
        if (lit->isEquality() && !lit->isPositive()) {
          lit = Kernel::Literal::create2(neqPredicate, true,
              *lit->nthArgument(0), *lit->nthArgument(1));
          changed = true;
        }
        literals.push(lit);
      }
      if (changed) it.replace(Kernel::Clause::fromStack(literals, clause->inference()));
    } else {
      Kernel::FormulaUnit *fu = static_cast<Kernel::FormulaUnit *>(unit);
      Kernel::Formula *replaced = replaceNegativeEquality(fu->formula(), neqPredicate);
      if (replaced != fu->formula()) {
        it.replace(new Kernel::FormulaUnit(replaced, fu->inference()));
      }
    }
  }

  // A clause is implicitly universally quantified, so this unit is exactly
  // the axiom ∀x ¬neq(x,x).
  Lib::Stack<Kernel::Literal *> axiomLiterals;
  axiomLiterals.push(Kernel::Literal::create2(neqPredicate, false,
      Kernel::TermList::var(0), Kernel::TermList::var(0)));
  Kernel::Clause *axiom = Kernel::Clause::fromStack(
      axiomLiterals, Kernel::Inference(Kernel::FromInput(Kernel::UnitInputType::AXIOM)));
  Kernel::UnitList::push(axiom, prb.units());
}

} // namespace

/**
 * @brief Controlla se un letterale contiene esclusivamente la variabile specificata (targetVar) o nessuna variabile.
 */
bool Lemma5::isUnaryOnVar(Kernel::Literal* lit, unsigned targetVar)
{
  if (!lit || lit->isEquality()) {
    return false;
  }

  bool hasOther = false;

  Kernel::VariableIterator vit(lit);
  while (vit.hasNext()) {
    Kernel::TermList tl = vit.next();
    unsigned var = tl.var();
    if (var != targetVar) hasOther = true;
  }

  // A nullary literal belongs to both γ(x) and δ(y): it contains neither
  // variable, so assigning it to γ is a valid decomposition.
  return !hasOther;
}

/**
 * @brief Rinombra la variabile 1 (Y) in 0 (X) all'interno di un letterale unario.
 */
Kernel::Literal* Lemma5::renameVariable(Kernel::Literal* lit, unsigned fromVar, unsigned toVar)
{
  if (!lit || lit->isEquality() || fromVar == toVar) {
    return lit;
  }
  Kernel::RobSubstitution subst;
  if (!subst.unify(Kernel::TermList::var(fromVar), 0,
                   Kernel::TermList::var(toVar), 1)) return lit;
  return subst.apply(lit, 0);
}

/**
 * @brief Crea una formula di disgiunzione (OR) a partire da un vettore di letterali.
 */
Kernel::Formula* Lemma5::createDisjunctionFromLiterals(const std::vector<Kernel::Literal*>& lits)
{
  if (lits.empty()) {
    return new Kernel::Formula(false);
  }

  if (lits.size() == 1) {
    return new Kernel::AtomicFormula(lits[0]);
  }

  Kernel::FormulaList* formLits = Kernel::FormulaList::empty();
  for (Kernel::Literal* lit : lits) {
    Kernel::FormulaList::push(new Kernel::AtomicFormula(lit), formLits);
  }
  formLits = Kernel::FormulaList::reverse(formLits);

  return Kernel::JunctionFormula::generalJunction(Kernel::OR, formLits);
}

/**
 * @brief Estrae tutti i letterali da una formula che rappresenta una disgiunzione o un letterale singolo.
 */
bool Lemma5::extractLiteralsFromFormula(Kernel::Formula* form, std::vector<Kernel::Literal*>& lits)
{
  if (!form) return false;

  if (form->connective() == Kernel::LITERAL) {
    lits.push_back(form->literal());
    return true;
  }

  if (form->connective() == Kernel::NOT && form->uarg()->connective() == Kernel::LITERAL) {
    Kernel::Literal* inner = form->uarg()->literal();
    lits.push_back(Kernel::Literal::create(inner, !inner->isPositive()));
    return true;
  }

  if (form->connective() == Kernel::OR) {
    Kernel::FormulaList::Iterator it(form->args());
    while (it.hasNext()) {
      if (!extractLiteralsFromFormula(it.next(), lits)) {
        return false;
      }
    }
    return true;
  }

  if (form->connective() == Kernel::FORALL) {
    return extractLiteralsFromFormula(form->qarg(), lits);
  }

  return false;
}

/**
 * @brief Decompone una lista di letterali separando l'uguaglianza positiva x = y dai letterali unari gamma(x) e delta(y).
 */
bool Lemma5::decomposeLiterals(const std::vector<Kernel::Literal*>& lits, std::vector<Kernel::Literal*>& gammaLits, std::vector<Kernel::Literal*>& deltaLits)
{
  unsigned xVar = 0;
  unsigned yVar = 0;
  bool hasPositiveEq = false;

  // Find the distinguished equality first. Literals can arrive in any order;
  // classifying unary literals before locating x=y would assume x=0,y=0.
  for (Kernel::Literal* lit : lits) {
    if (lit->isEquality() && lit->isPositive()) {
      Kernel::TermList arg0 = *lit->nthArgument(0);
      Kernel::TermList arg1 = *lit->nthArgument(1);
      if (arg0.isVar() && arg1.isVar() && arg0.var() != arg1.var()) {
        if (hasPositiveEq) {
          bool samePair = (arg0.var() == xVar && arg1.var() == yVar) ||
                          (arg0.var() == yVar && arg1.var() == xVar);
          if (!samePair) return false;
        } else {
          xVar = arg0.var();
          yVar = arg1.var();
        }
        hasPositiveEq = true;
      }
    }
  }
  if (!hasPositiveEq) return false;

  for (Kernel::Literal* lit : lits) {
    if (lit->isEquality() && lit->isPositive()) {
      Kernel::TermList arg0 = *lit->nthArgument(0);
      Kernel::TermList arg1 = *lit->nthArgument(1);
      if (arg0.isVar() && arg1.isVar() &&
          ((arg0.var() == xVar && arg1.var() == yVar) ||
           (arg0.var() == yVar && arg1.var() == xVar))) {
        continue;
      }
    }
    if (isUnaryOnVar(lit, xVar)) {
      gammaLits.push_back(renameVariable(lit, xVar, 0));
    } else if (isUnaryOnVar(lit, yVar)) {
      deltaLits.push_back(renameVariable(lit, yVar, 0));
    } else {
      return false;
    }
  }

  return hasPositiveEq;
}

/**
 * @brief Decompone una clausola di Tipo 3 isolando l'uguaglianza x = y e dividendo i letterali in gamma(x) e delta(y).
 */
bool Lemma5::decomposeType3Clause(Kernel::Clause* cl, std::vector<Kernel::Literal*>& gammaLits, std::vector<Kernel::Literal*>& deltaLits)
{
  if (!cl) return false;

  std::vector<Kernel::Literal*> lits;
  lits.reserve(cl->length());
  for (unsigned i = 0; i < cl->length(); i++) {
    lits.push_back((*cl)[i]);
  }

  return decomposeLiterals(lits, gammaLits, deltaLits);
}

/**
 * @brief Applica il Lemma 5 per trasformare le formule/clausole di Tipo 3 con uguaglianza x = y nei 3 rami dell'equivalenza.
 */
void Lemma5::applyLemma5(Kernel::Problem &prb)
{
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 5] INIZIO APPLICAZIONE LEMMA 5");
  }

  // Lemma 5's decomposition is expressed using the canonical variables x=0
  // and y=1. Lemma 4 may leave gaps in variable numbers (e.g. x=0,y=2), so
  // rectify the transformed formulas before recognizing that pattern.
  Shell::Rectify::rectify(prb.units());
  eliminateNegativeEqualities(prb);

  const Kernel::TermList sort = Kernel::AtomicSort::defaultSort();
  UnitList* newUnits = UnitList::empty();
  unsigned transformedCount = 0;

  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    Kernel::Unit* unit = it.next();
    std::vector<Kernel::Literal*> gammaLits;
    std::vector<Kernel::Literal*> deltaLits;
    bool canTransform = false;

    if (unit->isClause()) {
      Kernel::Clause* cl = static_cast<Kernel::Clause*>(unit);
      canTransform = decomposeType3Clause(cl, gammaLits, deltaLits);
    } else {
      Kernel::FormulaUnit* fu = static_cast<Kernel::FormulaUnit*>(unit);
      std::vector<Kernel::Literal*> lits;
      if (extractLiteralsFromFormula(fu->formula(), lits)) {
        canTransform = decomposeLiterals(lits, gammaLits, deltaLits);
      }
    }

    if (canTransform) {
      transformedCount++;
      if (FO2Logger::showsDebug()) {
        FO2Logger::logDebug("[Lemma 5] Trasformazione unita' di Tipo 3 con uguaglianza: " + unit->toString());
      }

      Kernel::Formula* gammaX = createDisjunctionFromLiterals(gammaLits);
      Kernel::Formula* deltaX = createDisjunctionFromLiterals(deltaLits);
      (void)deltaX;

      std::vector<Kernel::Literal*> deltaLitsX;
      for (Kernel::Literal* lit : deltaLits) {
        deltaLitsX.push_back(lit);
      }
      Kernel::Formula* deltaX0 = createDisjunctionFromLiterals(deltaLitsX);

      std::vector<Kernel::Literal*> gammaLitsY;
      for (Kernel::Literal* lit : gammaLits) {
        gammaLitsY.push_back(renameVariable(lit, 0, 1));
      }
      Kernel::Formula* gammaY = createDisjunctionFromLiterals(gammaLitsY);

      Kernel::Formula* ramo1 = new Kernel::QuantifiedFormula(Kernel::FORALL, Kernel::VSList::singleton({0u, sort}), gammaX);
      Kernel::Formula* ramo2 = new Kernel::QuantifiedFormula(Kernel::FORALL, Kernel::VSList::singleton({0u, sort}), deltaX0);

      Kernel::Formula* notGammaX = new Kernel::NegatedFormula(gammaX);
      Kernel::Formula* notGammaY = new Kernel::NegatedFormula(gammaY);

      Kernel::Literal* eqLit = Kernel::Literal::createEquality(true, Kernel::TermList::var(0), Kernel::TermList::var(1), sort);
      Kernel::Formula* impEq = new Kernel::BinaryFormula(Kernel::IMP, notGammaY, new Kernel::AtomicFormula(eqLit));
      Kernel::Formula* forallYImp = new Kernel::QuantifiedFormula(Kernel::FORALL, Kernel::VSList::singleton({1u, sort}), impEq);

      Kernel::FormulaList* andArgs1 = Kernel::FormulaList::empty();
      Kernel::FormulaList::push(forallYImp, andArgs1);
      Kernel::FormulaList::push(notGammaX, andArgs1);
      Kernel::Formula* existsUniqueBody = Kernel::JunctionFormula::generalJunction(Kernel::AND, andArgs1);
      Kernel::Formula* existsUnique = new Kernel::QuantifiedFormula(Kernel::EXISTS, Kernel::VSList::singleton({0u, sort}), existsUniqueBody);

      Kernel::Formula* coimp = new Kernel::QuantifiedFormula(Kernel::FORALL, Kernel::VSList::singleton({0u, sort}),
                                                             new Kernel::BinaryFormula(Kernel::IFF, gammaX, deltaX0));

      Kernel::FormulaList* andArgs2 = Kernel::FormulaList::empty();
      Kernel::FormulaList::push(coimp, andArgs2);
      Kernel::FormulaList::push(existsUnique, andArgs2);
      Kernel::Formula* ramo3 = Kernel::JunctionFormula::generalJunction(Kernel::AND, andArgs2);

      Kernel::FormulaList* branches = Kernel::FormulaList::empty();
      Kernel::FormulaList::push(ramo3, branches);
      Kernel::FormulaList::push(ramo2, branches);
      Kernel::FormulaList::push(ramo1, branches);
      Kernel::Formula* finalFormula = Kernel::JunctionFormula::generalJunction(Kernel::OR, branches);
      Kernel::Unit* newUnit = new Kernel::FormulaUnit(finalFormula, Kernel::Inference(Kernel::FromInput(Kernel::UnitInputType::AXIOM)));
      Kernel::UnitList::push(newUnit, newUnits);
      continue;
    }

    Kernel::UnitList::push(unit, newUnits);
  }

  prb.units() = Kernel::UnitList::reverse(newUnits);

  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 5] Trasformazione completata. Clausole modificate: " + std::to_string(transformedCount));
  }
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 5] FINE LEMMA 5");
  }
}

} // namespace Lemmata
} // namespace FO2Fragment
