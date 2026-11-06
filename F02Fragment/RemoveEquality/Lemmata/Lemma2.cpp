#include "Lemma2.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/List.hpp"
#include "Lib/Environment.hpp"
#include "Shell/NNF.hpp"
#include "Shell/Rectify.hpp"
#include "F02Fragment/FO2Logger.hpp"

#include <algorithm>
#include <set>
#include <vector>

using namespace Kernel;

namespace FO2Fragment {
namespace {

struct DefinitionBuilder {
  std::vector<Formula *> definitions;
  unsigned nextVariable = 0;

  unsigned freshVariable()
  {
    return nextVariable++;
  }

  static std::vector<unsigned> variablesOf(const Formula *formula)
  {
    std::set<unsigned> vars;
    collectFreeVariables(formula, vars);
    return std::vector<unsigned>(vars.begin(), vars.end());
  }

  static void collectFreeVariables(const Formula *formula, std::set<unsigned> &vars)
  {
    if (!formula) return;
    switch (formula->connective()) {
      case LITERAL: {
        VariableIterator it(formula->literal());
        while (it.hasNext()) vars.insert(it.next().var());
        return;
      }
      case NOT:
        collectFreeVariables(formula->uarg(), vars);
        return;
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) collectFreeVariables(it.next(), vars);
        return;
      }
      case IMP:
      case IFF:
      case XOR:
        collectFreeVariables(formula->left(), vars);
        collectFreeVariables(formula->right(), vars);
        return;
      case FORALL:
      case EXISTS: {
        std::set<unsigned> inner;
        collectFreeVariables(formula->qarg(), inner);
        VSList::Iterator it(formula->vars());
        while (it.hasNext()) inner.erase(it.next().first);
        vars.insert(inner.begin(), inner.end());
        return;
      }
      default:
        return;
    }
  }

  Literal *predicateLiteral(unsigned predicate, const std::vector<unsigned> &vars,
                            bool positive = true)
  {
    if (vars.empty()) return Literal::create(predicate, positive, {});
    if (vars.size() == 1) return Literal::create1(predicate, positive, TermList::var(vars[0]));
    if (vars.size() == 2) {
      return Literal::create2(predicate, positive, TermList::var(vars[0]), TermList::var(vars[1]));
    }
    return nullptr;
  }

  Literal *newPredicateLiteral(const std::vector<unsigned> &vars)
  {
    unsigned pred = env.signature->addFreshPredicate(vars.size(), "p_scott");
    return predicateLiteral(pred, vars);
  }

  static Literal *negate(Literal *lit)
  {
    return Literal::create(lit, !lit->isPositive());
  }

  Formula *clauseFormula(const std::vector<Literal *> &lits)
  {
    if (lits.empty()) return Formula::falseFormula();
    if (lits.size() == 1) return new AtomicFormula(lits.front());
    FormulaList *args = FormulaList::empty();
    for (auto it = lits.rbegin(); it != lits.rend(); ++it) {
      FormulaList::push(new AtomicFormula(*it), args);
    }
    return JunctionFormula::generalJunction(OR, args);
  }

  Formula *universallyQuantified(Formula *matrix, std::vector<unsigned> vars)
  {
    // Scott Type 3 requires two universal variables. Unused variables may be
    // added because first-order structures have a non-empty domain.
    while (vars.size() < 2) vars.push_back(freshVariable());
    if (vars.size() > 2) return nullptr;
    const TermList sort = AtomicSort::defaultSort();
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
      matrix = new QuantifiedFormula(FORALL, VSList::singleton({*it, sort}), matrix);
    }
    return matrix;
  }

  Formula *universallyThenExistentially(Formula *matrix, const std::vector<unsigned> &freeVars,
                                       unsigned existentialVar)
  {
    if (freeVars.size() > 1) return nullptr;
    const TermList sort = AtomicSort::defaultSort();
    matrix = new QuantifiedFormula(EXISTS, VSList::singleton({existentialVar, sort}), matrix);
    if (!freeVars.empty()) {
      matrix = new QuantifiedFormula(FORALL, VSList::singleton({freeVars.front(), sort}), matrix);
    }
    return matrix;
  }

  Formula *existentiallyQuantified(Formula *matrix, unsigned var)
  {
    return new QuantifiedFormula(EXISTS,
        VSList::singleton({var, AtomicSort::defaultSort()}), matrix);
  }

  void addUniversalClause(const std::vector<Literal *> &lits,
                          const std::vector<unsigned> &vars)
  {
    Formula *formula = universallyQuantified(clauseFormula(lits), vars);
    if (formula) definitions.push_back(formula);
  }

  Literal *nameFormula(Formula *formula)
  {
    if (!formula) return nullptr;
    if (formula->connective() == LITERAL) return formula->literal();

    // NNF has only literals, conjunctions/disjunctions, and quantifiers.
    if (formula->connective() == TRUE || formula->connective() == FALSE) {
      unsigned p = env.signature->addFreshPredicate(0, "p_scott_const");
      Literal *atom = predicateLiteral(p, {});
      std::vector<Literal *> unit{formula->connective() == TRUE ? atom : negate(atom)};
      addUniversalClause(unit, {});
      return atom;
    }

    // Rectification normally leaves one variable per quantifier node. Split
    // any bundled variables into nested quantifiers before naming the formula.
    if ((formula->connective() == FORALL || formula->connective() == EXISTS)) {
      std::vector<std::pair<unsigned, TermList>> bound;
      VSList::Iterator it(formula->vars());
      while (it.hasNext()) bound.push_back(it.next());
      if (bound.size() != 1) {
        Formula *nested = formula->qarg();
        for (auto bit = bound.rbegin(); bit != bound.rend(); ++bit) {
          nested = new QuantifiedFormula(formula->connective(),
              VSList::singleton({bit->first, bit->second}), nested);
        }
        return nameFormula(nested);
      }
    }

    std::vector<unsigned> freeVars = variablesOf(formula);
    if (freeVars.size() > 2) return nullptr; // Outside L2.
    Literal *name = newPredicateLiteral(freeVars);

    if (formula->connective() == AND || formula->connective() == OR) {
      std::vector<Literal *> children;
      FormulaList::Iterator it(formula->args());
      while (it.hasNext()) {
        Literal *child = nameFormula(it.next());
        if (!child) return nullptr;
        children.push_back(child);
      }
      if (formula->connective() == AND) {
        for (Literal *child : children) {
          addUniversalClause({negate(name), child}, freeVars);
        }
        std::vector<Literal *> reverseDirection{ name };
        for (Literal *child : children) reverseDirection.push_back(negate(child));
        addUniversalClause(reverseDirection, freeVars);
      } else {
        std::vector<Literal *> forwardDirection{ negate(name) };
        forwardDirection.insert(forwardDirection.end(), children.begin(), children.end());
        addUniversalClause(forwardDirection, freeVars);
        for (Literal *child : children) {
          addUniversalClause({name, negate(child)}, freeVars);
        }
      }
      return name;
    }

    if (formula->connective() == FORALL || formula->connective() == EXISTS) {
      unsigned quantifiedVar = firstBoundVariable(formula);
      Literal *body = nameFormula(formula->qarg());
      if (!body) return nullptr;
      if (formula->connective() == EXISTS) {
        Formula *witnessClause = universallyThenExistentially(
            clauseFormula({negate(name), body}), freeVars, quantifiedVar);
        if (witnessClause) definitions.push_back(witnessClause);
        addUniversalClause({name, negate(body)},
                           withVariable(freeVars, quantifiedVar));
      } else {
        addUniversalClause({negate(name), body}, withVariable(freeVars, quantifiedVar));
        Formula *counterexampleClause = universallyThenExistentially(
            clauseFormula({name, negate(body)}), freeVars, quantifiedVar);
        if (counterexampleClause) definitions.push_back(counterexampleClause);
      }
      return name;
    }

    return nullptr;
  }

  static unsigned firstBoundVariable(const Formula *formula)
  {
    VSList::Iterator it(formula->vars());
    return it.next().first;
  }

  static void collectAllVariables(const Formula *formula, unsigned &maximum, bool &found)
  {
    if (!formula) return;
    switch (formula->connective()) {
      case LITERAL: {
        VariableIterator it(formula->literal());
        while (it.hasNext()) {
          unsigned var = it.next().var();
          maximum = found ? std::max(maximum, var) : var;
          found = true;
        }
        return;
      }
      case NOT:
        collectAllVariables(formula->uarg(), maximum, found);
        return;
      case AND:
      case OR: {
        FormulaList::Iterator it(formula->args());
        while (it.hasNext()) collectAllVariables(it.next(), maximum, found);
        return;
      }
      case IMP:
      case IFF:
      case XOR:
        collectAllVariables(formula->left(), maximum, found);
        collectAllVariables(formula->right(), maximum, found);
        return;
      case FORALL:
      case EXISTS: {
        VSList::Iterator it(formula->vars());
        while (it.hasNext()) {
          unsigned var = it.next().first;
          maximum = found ? std::max(maximum, var) : var;
          found = true;
        }
        collectAllVariables(formula->qarg(), maximum, found);
        return;
      }
      default:
        return;
    }
  }

  static std::vector<unsigned> withVariable(std::vector<unsigned> vars, unsigned var)
  {
    vars.push_back(var);
    std::sort(vars.begin(), vars.end());
    vars.erase(std::unique(vars.begin(), vars.end()), vars.end());
    return vars;
  }

  Formula *rootAssertion(Literal *root)
  {
    if (!root) return Formula::falseFormula();
    // Input formulas are sentences. A nullary root is asserted with Type 1;
    // if it is already a literal, a fresh variable provides a harmless wrapper.
    if (root->arity() == 0) {
      return existentiallyQuantified(new AtomicFormula(root), freshVariable());
    }
    return nullptr;
  }
};

} // namespace

void Lemma2::applyLemma2(Kernel::Problem &prb)
{
  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 2] Converting formulas to Scott normal form");
  }

  UnitList *generatedDefinitions = UnitList::empty();
  UnitList::DelIterator it(prb.units());
  while (it.hasNext()) {
    Unit *unit = it.next();
    if (unit->isClause()) continue;

    FormulaUnit *original = static_cast<FormulaUnit *>(unit);
    FormulaUnit *normalized = Shell::Rectify::rectify(original);
    normalized = Shell::NNF::nnf(normalized);

    DefinitionBuilder builder;
    Formula *matrix = normalized->formula();
    unsigned maximum = 0;
    bool foundVariable = false;
    DefinitionBuilder::collectAllVariables(matrix, maximum, foundVariable);
    builder.nextVariable = foundVariable ? maximum + 1 : 0;
    Literal *root = builder.nameFormula(matrix);
    if (!root) continue;
    Formula *assertion = builder.rootAssertion(root);

    if (!assertion) {
      // The input was not a closed L2 sentence or exceeded the supported
      // variable bound. Keep it intact so later validation can report it.
      continue;
    }

    FormulaUnit *rootUnit = new FormulaUnit(assertion,
        NonspecificInference1(InferenceRule::INPUT, unit));
    it.replace(rootUnit);

    while (!builder.definitions.empty()) {
      Formula *definition = builder.definitions.back();
      builder.definitions.pop_back();
      UnitList::push(new FormulaUnit(definition,
          Inference(FromInput(UnitInputType::AXIOM))), generatedDefinitions);
    }
  }

  prb.units() = UnitList::concat(generatedDefinitions, prb.units());

  if (FO2Logger::showsDebug()) {
    FO2Logger::logDebug("[Lemma 2] Scott normal form conversion complete");
  }
}

} // namespace FO2Fragment
