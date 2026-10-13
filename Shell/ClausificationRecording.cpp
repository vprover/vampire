/*
 * This file is part of Vampire, distributed under the licence found at
 * https://vprover.github.io/license.html and in the source directory.
 */
#include "ClausificationRecording.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/TermIterators.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"

#include <set>

namespace Shell {
using namespace Kernel;

std::string replayFormula(Formula* formula)
{
  return std::string(env.higherOrder() ? "$thf(" : "$tff(") + formula->toString() + ")";
}

std::string replayFOOLTerm(TermList term)
{
  if (term.isTerm() && term.term()->isFormula()) {
    return replayFormula(term.term()->getSpecialData()->getFormula());
  }
  return std::string(env.higherOrder() ? "$thf(" : "$fot(") + term.toString() + ")";
}

namespace {
/** Strip the explicit universal prefix, preserving the declared binder order.
 * Repeated binder names would require scope-aware renaming, outside this
 * certificate's scope. Leave the body in formula. */
bool collectUniversalBinders(Formula*& formula, std::vector<unsigned>& binders,
                             std::set<unsigned>& seen)
{
  while (formula->connective() == FORALL) {
    VSList::Iterator variables(formula->vars());
    while (variables.hasNext()) {
      unsigned variable = variables.next().first;
      if (!seen.insert(variable).second) { return false; }
      binders.push_back(variable);
    }
    formula = formula->qarg();
  }
  return true;
}

/** Formula::toString prints junction arguments in reverse list order. Use
 * that same order, keeping every occurrence and its printed equality sides.
 * An explicit stack avoids recursion on deeply nested disjunctions. */
bool collectPrintedOccurrences(Formula* formula,
                               std::vector<ClausificationExtra::Occurrence>& occurrences)
{
  Lib::Stack<Formula*> pending;
  pending.push(formula);
  while (pending.isNonEmpty()) {
    Formula* next = pending.pop();
    switch (next->connective()) {
    case LITERAL: {
      Literal* literal = next->literal();
      occurrences.push_back({literal,
          literal->isEquality() && static_cast<AtomicFormula*>(next)->flipForPrinting});
      break;
    }
    case FALSE:
      break;
    case OR: {
      FormulaList::Iterator args(next->args());
      while (args.hasNext()) { pending.push(args.next()); }
      break;
    }
    default:
      return false;
    }
  }
  return true;
}
} // namespace

void recordClausification(FormulaUnit* parent, Clause* conclusion)
{
  if (env.options->proofExtra() != Options::ProofExtra::REPLAY) { return; }
  Formula* body = parent->formula();
  std::vector<unsigned> binders;
  std::set<unsigned> seen;
  ClausificationExtra information;
  if (!collectUniversalBinders(body, binders, seen) ||
      !collectPrintedOccurrences(body, information.occurrences) ||
      information.occurrences.size() != conclusion->length()) { return; }

  // Free variables act as implicit universal binders, after the explicit ones.
  for (auto occurrence : information.occurrences) {
    VariableIterator variables(occurrence.instantiated);
    while (variables.hasNext()) {
      unsigned variable = variables.next().var();
      if (seen.insert(variable).second) { binders.push_back(variable); }
    }
  }
  std::set<unsigned> targetVariables;
  auto variables = conclusion->getVariableIterator();
  while (variables.hasNext()) { targetVariables.insert(variables.next()); }
  for (unsigned variable : binders) {
    // Old CNF drops universal binders without renaming. A vacuous binder has
    // no conclusion variable, so cannot be represented by this mapping.
    if (!targetVariables.contains(variable)) { return; }
    information.binders.emplace_back(variable, variable);
  }
  env.proofExtra.insert(conclusion, new ClausificationExtra(std::move(information)));
}

} // namespace Shell
