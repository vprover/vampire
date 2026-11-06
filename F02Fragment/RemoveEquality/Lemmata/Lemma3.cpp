#include "Lemma3.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/List.hpp"
#include "F02Fragment/FO2Logger.hpp"

#include <vector>

using namespace Kernel;

namespace FO2Fragment {
namespace {

Formula *makeEquality(bool positive, unsigned x, unsigned y)
{
  return new AtomicFormula(Literal::createEquality(
      positive, TermList::var(x), TermList::var(y), AtomicSort::defaultSort()));
}

Formula *makeJunction(Connective connective, Formula *left, Formula *right)
{
  FormulaList *args = FormulaList::empty();
  FormulaList::push(right, args);
  FormulaList::push(left, args);
  return JunctionFormula::generalJunction(connective, args);
}

bool containsEquality(const Formula *formula)
{
  if (!formula) return false;
  switch (formula->connective()) {
    case LITERAL:
      return formula->literal() && formula->literal()->isEquality();
    case NOT:
      return containsEquality(formula->uarg());
    case AND:
    case OR: {
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) if (containsEquality(it.next())) return true;
      return false;
    }
    case IMP:
    case IFF:
    case XOR:
      return containsEquality(formula->left()) || containsEquality(formula->right());
    case FORALL:
    case EXISTS:
      return containsEquality(formula->qarg());
    default:
      return false;
  }
}

bool isLiteralOrClause(const Formula *formula)
{
  if (!formula) return false;
  if (formula->connective() == LITERAL || formula->connective() == TRUE ||
      formula->connective() == FALSE) return true;
  if (formula->connective() != OR) return false;
  FormulaList::Iterator it(formula->args());
  while (it.hasNext()) {
    Formula *arg = it.next();
    if (arg->connective() != LITERAL && arg->connective() != TRUE &&
        arg->connective() != FALSE) return false;
  }
  return true;
}

bool isCnf(const Formula *formula)
{
  if (isLiteralOrClause(formula)) return true;
  if (!formula || formula->connective() != AND) return false;
  FormulaList::Iterator it(formula->args());
  while (it.hasNext()) if (!isLiteralOrClause(it.next())) return false;
  return true;
}

Formula *substituteVariable(Formula *formula, unsigned from, unsigned to)
{
  if (!formula) return nullptr;
  switch (formula->connective()) {
    case LITERAL: {
      Literal *literal = formula->literal();
      std::vector<TermList> arguments;
      arguments.reserve(literal->arity());
      for (unsigned i = 0; i < literal->arity(); ++i) {
        TermList argument = *literal->nthArgument(i);
        if (argument.isVar() && argument.var() == from) argument = TermList::var(to);
        arguments.push_back(argument);
      }
      Literal *substituted = literal->isEquality()
          ? Literal::createEquality(literal->isPositive(), arguments[0], arguments[1],
                literal->isTwoVarEquality() ? literal->twoVarEqSort() : AtomicSort::defaultSort())
          : Literal::create(literal->functor(), literal->arity(), literal->isPositive(), arguments.data());
      return new AtomicFormula(substituted);
    }
    case NOT:
      return new NegatedFormula(substituteVariable(formula->uarg(), from, to));
    case AND:
    case OR: {
      FormulaList *args = FormulaList::empty();
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) FormulaList::push(substituteVariable(it.next(), from, to), args);
      return JunctionFormula::generalJunction(formula->connective(), FormulaList::reverse(args));
    }
    default:
      return formula;
  }
}

/** Evaluate x=y literals under a supplied diagonal/off-diagonal case. */
Formula *simplifyEqualityUnderRelation(Formula *formula, unsigned x, unsigned y,
                                       bool pairEqual)
{
  if (!formula) return nullptr;
  switch (formula->connective()) {
    case LITERAL: {
      Literal *lit = formula->literal();
      if (!lit || !lit->isEquality()) return formula;
      TermList a = *lit->nthArgument(0), b = *lit->nthArgument(1);
      if (!a.isVar() || !b.isVar()) return formula;
      const bool reflexive = a.var() == b.var();
      const bool guardedPair = (a.var() == x && b.var() == y) ||
                               (a.var() == y && b.var() == x);
      if (!reflexive && !guardedPair) return formula;
      const bool equalityTrue = reflexive || (guardedPair && pairEqual);
      const bool literalTrue = lit->isPositive() ? equalityTrue : !equalityTrue;
      return literalTrue ? Formula::trueFormula() : Formula::falseFormula();
    }
    case NOT: {
      Formula *arg = simplifyEqualityUnderRelation(formula->uarg(), x, y, pairEqual);
      if (arg->connective() == TRUE) return Formula::falseFormula();
      if (arg->connective() == FALSE) return Formula::trueFormula();
      return arg == formula->uarg() ? formula : new NegatedFormula(arg);
    }
    case AND:
    case OR: {
      FormulaList *args = FormulaList::empty();
      bool changed = false;
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {
        Formula *oldArg = it.next();
        Formula *arg = simplifyEqualityUnderRelation(oldArg, x, y, pairEqual);
        changed = changed || arg != oldArg;
        const bool identity = (formula->connective() == AND && arg->connective() == TRUE) ||
                              (formula->connective() == OR && arg->connective() == FALSE);
        const bool annihilator = (formula->connective() == AND && arg->connective() == FALSE) ||
                                 (formula->connective() == OR && arg->connective() == TRUE);
        if (annihilator) {
          FormulaList::destroy(args);
          return formula->connective() == AND ? Formula::falseFormula() : Formula::trueFormula();
        }
        if (identity) { changed = true; continue; }
        FormulaList::push(arg, args);
      }
      args = FormulaList::reverse(args);
      if (!changed) { FormulaList::destroy(args); return formula; }
      if (!args) return formula->connective() == AND ? Formula::trueFormula() : Formula::falseFormula();
      return JunctionFormula::generalJunction(formula->connective(), args);
    }
    default:
      // Lemma 2 produces NNF clause matrices. A remaining non-NNF connective
      // is left unchanged because Lemma 3 only rewrites clause matrices.
      return formula;
  }
}

Formula *addEqualityToCnf(unsigned x, unsigned y, Formula *cnf)
{
  if (cnf->connective() != AND) return makeJunction(OR, makeEquality(true, x, y), cnf);
  FormulaList *clauses = FormulaList::empty();
  FormulaList::Iterator it(cnf->args());
  while (it.hasNext()) {
    FormulaList::push(makeJunction(OR, makeEquality(true, x, y), it.next()), clauses);
  }
  return JunctionFormula::generalJunction(AND, FormulaList::reverse(clauses));
}

unsigned firstBoundVariable(const Formula *formula)
{
  VSList::Iterator it(formula->vars());
  return it.next().first;
}

Formula *transformScottFormula(Formula *formula)
{
  if (!formula) return formula;

  // Type 1: ∃x α. Its matrix contains at most x, so equality is reflexive.
  if (formula->connective() == EXISTS) {
    unsigned x = firstBoundVariable(formula);
    Formula *matrix = simplifyEqualityUnderRelation(formula->qarg(), x, x, true);
    if (matrix != formula->qarg() && !containsEquality(matrix)) {
      return new QuantifiedFormula(EXISTS, formula->vars(), matrix);
    }
    return formula;
  }

  // Type 2: split the witness into the diagonal case and the distinct case.
  // This is the standard equivalence
  //   forall x exists y A(x,y)
  //   <=> forall x (A(x,x) or exists y (x!=y and A(x,y))).
  // Keeping x!=y as an unconditional conjunct loses singleton models and,
  // more generally, witnesses that can only be chosen on the diagonal.
  if (formula->connective() == FORALL && formula->qarg() &&
      formula->qarg()->connective() == EXISTS) {
    Formula *exists = formula->qarg();
    unsigned x = firstBoundVariable(formula), y = firstBoundVariable(exists);
    Formula *matrix = exists->qarg();
    Formula *diagonal = simplifyEqualityUnderRelation(
        substituteVariable(matrix, y, x), x, y, true);
    Formula *offDiagonal = simplifyEqualityUnderRelation(matrix, x, y, false);
    if (!isCnf(diagonal) || !isCnf(offDiagonal) ||
        containsEquality(diagonal) || containsEquality(offDiagonal)) return formula;

    Formula *distinctWitness = new QuantifiedFormula(EXISTS, exists->vars(),
        makeJunction(AND, makeEquality(false, x, y), offDiagonal));
    Formula *choice = makeJunction(OR, diagonal, distinctWitness);
    return new QuantifiedFormula(FORALL, formula->vars(),
        choice);
  }

  // Type 3: put the universal matrix in the guarded form from Lemma 3.
  if (formula->connective() == FORALL) {
    Formula *matrix = formula;
    unsigned vars[2], count = 0;
    while (matrix && matrix->connective() == FORALL) {
      VSList::Iterator it(matrix->vars());
      while (it.hasNext()) {
        if (count == 2) return formula;
        vars[count++] = it.next().first;
      }
      matrix = matrix->qarg();
    }
    if (count == 2 && matrix && matrix->connective() != FORALL &&
        matrix->connective() != EXISTS) {
      // Split the universal case exactly: the off-diagonal matrix is guarded
      // by x=y, while the diagonal instance remains as a unary universal.
      // Keeping only the guarded Type 3 part loses constraints on x=y.
      Formula *diagonal = simplifyEqualityUnderRelation(
          substituteVariable(matrix, vars[1], vars[0]), vars[0], vars[1], true);
      Formula *offDiagonal = simplifyEqualityUnderRelation(matrix, vars[0], vars[1], false);
      if (!isCnf(diagonal) || containsEquality(diagonal) ||
          !isCnf(offDiagonal) || containsEquality(offDiagonal)) return formula;

      auto guardedType3 = [&](Formula *cnf) -> Formula * {
        Formula *guarded = addEqualityToCnf(vars[0], vars[1], cnf);
        Formula *prefix = formula;
        unsigned consumed = 0;
        while (prefix && prefix->connective() == FORALL && consumed < 2) {
          unsigned nvars = 0;
          VSList::Iterator it(prefix->vars());
          while (it.hasNext()) { it.next(); ++nvars; }
          if (consumed + nvars > 2) return nullptr;
          guarded = new QuantifiedFormula(FORALL, prefix->vars(), guarded);
          consumed += nvars;
          prefix = prefix->qarg();
        }
        return consumed == 2 ? guarded : nullptr;
      };

      Formula *offDiagonalGuard = guardedType3(offDiagonal);
      if (!offDiagonalGuard) return formula;
      Formula *diagonalConstraint = new QuantifiedFormula(
          FORALL, VSList::singleton({vars[0], AtomicSort::defaultSort()}), diagonal);
      return makeJunction(AND, diagonalConstraint, offDiagonalGuard);
    }
  }
  return formula;
}

Formula *transformScottConjuncts(Formula *formula)
{
  if (!formula || formula->connective() != AND) return transformScottFormula(formula);
  FormulaList *args = FormulaList::empty();
  bool changed = false;
  FormulaList::Iterator it(formula->args());
  while (it.hasNext()) {
    Formula *oldArg = it.next();
    Formula *arg = transformScottConjuncts(oldArg);
    changed = changed || arg != oldArg;
    FormulaList::push(arg, args);
  }
  args = FormulaList::reverse(args);
  if (!changed) { FormulaList::destroy(args); return formula; }
  return JunctionFormula::generalJunction(AND, args);
}

} // namespace

void Lemma3::applyLemma3(Kernel::Problem &prb)
{
  UnitList *generated = UnitList::empty();
  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    Unit *unit = it.next();
    if (unit->isClause()) continue;
    FormulaUnit *fu = static_cast<FormulaUnit *>(unit);
    Formula *transformed = transformScottConjuncts(fu->formula());
    if (transformed != fu->formula()) {
      if (transformed->connective() == AND) {
        FormulaList::Iterator conjuncts(transformed->args());
        bool first = true;
        while (conjuncts.hasNext()) {
          FormulaUnit *newUnit = new FormulaUnit(conjuncts.next(),
              NonspecificInference1(InferenceRule::INPUT, unit));
          if (first) { it.replace(newUnit); first = false; }
          else UnitList::push(newUnit, generated);
        }
      } else {
        it.replace(new FormulaUnit(transformed, NonspecificInference1(InferenceRule::INPUT, unit)));
      }
    }
  }
  prb.units() = UnitList::concat(generated, prb.units());
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 3] Equality moved from Type 1/2/3 matrices into Scott guards.");
  }
}

} // namespace FO2Fragment
